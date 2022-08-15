use super::*;

pub trait Input {
    type Offset: Copy + Ord;
    type Token;
    type Span: Span;

    fn start(&self) -> Self::Offset;

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>);

    fn span(&self, range: Range<Self::Offset>) -> Self::Span;
}

pub trait SliceInput: Input {
    type Slice: ?Sized;

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice;
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice;
}

// Implemented by inputs that reference a string slice and use byte indices as their offset.
pub trait StrInput<C: Char>:
    Input<Offset = usize, Token = C> + SliceInput<Slice = C::Slice>
{
}

impl Input for str {
    type Offset = usize;
    type Token = char;
    type Span = Range<usize>;

    fn start(&self) -> Self::Offset {
        0
    }

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) {
        let chr = unsafe { self.get_unchecked(offset..).chars().next() };
        (offset + chr.map_or(0, char::len_utf8), chr)
    }

    fn span(&self, range: Range<Self::Offset>) -> Self::Span {
        range
    }
}

impl StrInput<char> for str {}

impl SliceInput for str {
    type Slice = str;

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice {
        &self[range]
    }
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice {
        &self[from]
    }
}

impl<T: Clone> Input for [T] {
    type Offset = usize;
    type Token = T;
    type Span = Range<usize>;

    fn start(&self) -> Self::Offset {
        0
    }

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) {
        if let Some(tok) = self.get(offset) {
            (offset + 1, Some(tok.clone()))
        } else {
            (offset, None)
        }
    }

    fn span(&self, range: Range<Self::Offset>) -> Self::Span {
        range
    }
}

impl StrInput<u8> for [u8] {}

impl<T: Clone> SliceInput for [T] {
    type Slice = [T];

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice {
        &self[range]
    }
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice {
        &self[from]
    }
}

pub struct WithContext<'a, Ctx, I: ?Sized>(pub Ctx, pub &'a I);

impl<'a, Ctx: Clone, I: Input + ?Sized> Input for WithContext<'a, Ctx, I> {
    type Offset = I::Offset;
    type Token = I::Token;
    type Span = (Ctx, I::Span);

    fn start(&self) -> Self::Offset {
        self.1.start()
    }

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) {
        self.1.next(offset)
    }

    fn span(&self, range: Range<Self::Offset>) -> Self::Span {
        (self.0.clone(), self.1.span(range))
    }
}

impl<'a, Ctx: Clone, I: SliceInput + ?Sized> SliceInput for WithContext<'a, Ctx, I> {
    type Slice = I::Slice;

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice {
        <I as SliceInput>::slice(&*self.1, range)
    }
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice {
        <I as SliceInput>::slice_from(&*self.1, from)
    }
}

impl<'a, Ctx, C, I> StrInput<C> for WithContext<'a, Ctx, I>
where
    Ctx: Clone,
    C: Char,
    I: Input<Token = C, Offset = usize> + SliceInput<Slice = C::Slice>,
{
}

// Represents the progress of a parser through the input
pub(crate) struct Marker<I: Input + ?Sized> {
    pos: usize,
    offset: I::Offset,
    err_count: usize,
}

impl<I: Input + ?Sized> Copy for Marker<I> {}
impl<I: Input + ?Sized> Clone for Marker<I> {
    fn clone(&self) -> Self {
        *self
    }
}

pub struct InputRef<'a, 'parse, I: Input + ?Sized, E: Error<I>, S> {
    input: &'a I,
    marker: Marker<I>,
    state: &'parse mut S,
    errors: Vec<E>,
}

impl<'a, 'parse, I: Input + ?Sized, E: Error<I>, S> InputRef<'a, 'parse, I, E, S> {
    pub(crate) fn new(input: &'a I, state: &'parse mut S) -> Self {
        Self {
            input,
            marker: Marker {
                pos: 0,
                offset: input.start(),
                err_count: 0,
            },
            state,
            errors: Vec::new(),
        }
    }

    pub(crate) fn save(&mut self) -> Marker<I> {
        self.marker
    }
    pub(crate) fn rewind(&mut self, marker: Marker<I>) {
        self.errors.truncate(marker.err_count);
        self.marker = marker;
    }

    pub(crate) fn state(&mut self) -> &mut S {
        self.state
    }

    pub(crate) fn skip_while<F: FnMut(&I::Token) -> bool>(&mut self, mut f: F) {
        loop {
            let before = self.save();
            if self.next().1.filter(&mut f).is_none() {
                self.rewind(before);
                break;
            }
        }
    }

    pub(crate) fn next(&mut self) -> (usize, Option<I::Token>) {
        let (offset, token) = self.input.next(self.marker.offset);
        self.marker.offset = offset;
        self.marker.pos += 1;
        (self.marker.pos, token)
    }

    pub(crate) fn last_pos(&self) -> usize {
        self.marker.pos
    }

    pub(crate) fn slice(&self, range: Range<Marker<I>>) -> &'a I::Slice
    where
        I: SliceInput,
    {
        self.input.slice(range.start.offset..range.end.offset)
    }

    pub(crate) fn slice_from(&self, from: RangeFrom<Marker<I>>) -> &'a I::Slice
    where
        I: SliceInput,
    {
        self.input.slice_from(from.start.offset..)
    }

    pub(crate) fn slice_trailing(&self) -> &'a I::Slice
    where
        I: SliceInput,
    {
        self.input.slice_from(self.marker.offset..)
    }

    pub(crate) fn span_since(&self, before: Marker<I>) -> I::Span {
        self.input.span(before.offset..self.marker.offset)
    }

    pub(crate) fn skip_bytes<C>(&mut self, skip: usize)
    where
        C: Char,
        I: StrInput<C>,
    {
        self.marker.offset += skip;
    }

    pub(crate) fn emit(&mut self, error: E) {
        self.errors.push(error);
    }

    pub(crate) fn into_errs(self) -> Vec<E> {
        self.errors
    }
}
