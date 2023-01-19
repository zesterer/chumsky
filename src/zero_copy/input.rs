//! Token input streams and tools converting to and from them..
//!
//! *“What’s up?” “I don’t know,” said Marvin, “I’ve never been there.”*
//!
//! [`Input`] is the primary trait used to feed input data into a chumsky parser. You can create them in a number of
//! ways: from strings, slices, arrays, etc.

use super::*;

/// A trait for types that represents a stream of input tokens. Unlike [`Iterator`], this type
/// supports backtracking and a few other features required by the crate.
pub trait Input {
    /// The type used to keep track of the current location in the stream
    type Offset: Copy + Ord;
    /// The type of singular items read from the stream
    type Token;
    /// The type of a span on this input - to provide custom span context see [`WithContext`]
    type Span: Span;

    /// Get the offset representing the start of this stream
    fn start(&self) -> Self::Offset;

    /// Get the next offset from the provided one, and the next token if it exists
    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>);

    /// Create a span from a start and end offset
    fn span(&self, range: Range<Self::Offset>) -> Self::Span;
}

/// A trait for types that represent slice-like streams of input tokens.
pub trait SliceInput: Input {
    /// The unsized slice type of this input. For [`&str`] it's `str`, and for [`&[T]`] it will be
    /// `[T]`
    type Slice: ?Sized;

    /// Get a slice from a start and end offset
    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice;
    /// Get a slice from a start offset till the end of the input
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice;
}

// Implemented by inputs that rference a string slice and use byte indices as their offset.
/// A trait for types that represent string-like streams of input tokens
pub trait StrInput<C: Char>:
    Input<Offset = usize, Token = C> + SliceInput<Slice = C::Slice>
{
}

impl Input for str {
    type Offset = usize;
    type Token = char;
    type Span = SimpleSpan<usize>;

    fn start(&self) -> Self::Offset {
        0
    }

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) {
        if offset < self.len() {
            let c = unsafe {
                self.get_unchecked(offset..)
                    .chars()
                    .next()
                    .unwrap_unchecked()
            };
            (offset + c.len_utf8(), Some(c))
        } else {
            (offset, None)
        }
    }

    fn span(&self, range: Range<Self::Offset>) -> Self::Span {
        range.into()
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
    type Span = SimpleSpan<usize>;

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
        range.into()
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

///
pub struct WithContext<'a, Ctx, In: ?Sized>(pub Ctx, pub &'a In);

impl<'a, Ctx: Clone, In: Input + ?Sized> Input for WithContext<'a, Ctx, In> {
    type Offset = In::Offset;
    type Token = In::Token;
    type Span = (Ctx, In::Span);

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

impl<'a, Ctx: Clone, In: SliceInput + ?Sized> SliceInput for WithContext<'a, Ctx, In> {
    type Slice = In::Slice;

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice {
        <In as SliceInput>::slice(&*self.1, range)
    }
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice {
        <In as SliceInput>::slice_from(&*self.1, from)
    }
}

impl<'a, Ctx, C, In> StrInput<C> for WithContext<'a, Ctx, In>
where
    Ctx: Clone,
    C: Char,
    In: Input<Token = C, Offset = usize> + SliceInput<Slice = C::Slice>,
{
}

// Represents the progress of a parser through the input
pub(crate) struct Marker<In: Input + ?Sized> {
    pos: usize,
    offset: In::Offset,
    err_count: usize,
}

impl<In: Input + ?Sized> Copy for Marker<In> {}
impl<In: Input + ?Sized> Clone for Marker<In> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Internal type representing an input as well as all the necessary context for parsing.
pub struct InputRef<'a, 'parse, In: Input + ?Sized, Err: Error<In>, State, Ctx> {
    input: &'a In,
    marker: Marker<In>,
    state: &'parse mut State,
    ctx: Ctx,
    errors: Vec<Err>,
}

impl<'a, 'parse, In: Input + ?Sized, Err: Error<In>, State, Ctx> InputRef<'a, 'parse, In, Err, State, Ctx> {
    pub(crate) fn new(input: &'a In, state: &'parse mut State) -> Self
    where
        Ctx: Default,
    {
        Self {
            input,
            marker: Marker {
                pos: 0,
                offset: input.start(),
                err_count: 0,
            },
            state,
            ctx: Ctx::default(),
            errors: Vec::new(),
        }
    }

    pub(crate) fn with_ctx<'sub_parse, CtxN, O>(
        &'sub_parse mut self,
        new_ctx: CtxN,
        f: impl FnOnce(&mut InputRef<'a, 'sub_parse, In, Err, State, CtxN>) -> O,
    ) -> O
    where
        'parse: 'sub_parse,
    {
        use core::mem;

        let mut new_ctx = InputRef {
            input: self.input,
            marker: self.marker,
            state: self.state,
            ctx: new_ctx,
            errors: mem::take(&mut self.errors),
        };
        let res = f(&mut new_ctx);
        self.marker = new_ctx.marker;
        self.errors = mem::take(&mut new_ctx.errors);
        res
    }

    pub(crate) fn save(&mut self) -> Marker<In> {
        self.marker
    }
    pub(crate) fn rewind(&mut self, marker: Marker<In>) {
        self.errors.truncate(marker.err_count);
        self.marker = marker;
    }

    pub(crate) fn state(&mut self) -> &mut State {
        self.state
    }

    pub(crate) fn ctx(&self) -> &Ctx {
        &self.ctx
    }

    pub(crate) fn skip_while<F: FnMut(&In::Token) -> bool>(&mut self, mut f: F) {
        loop {
            let (offset, token) = self.input.next(self.marker.offset);
            if token.filter(&mut f).is_none() {
                break
            } else {
                self.marker.offset = offset;
                self.marker.pos += 1;
            }
        }
    }

    pub(crate) fn next(&mut self) -> (usize, Option<In::Token>) {
        let (offset, token) = self.input.next(self.marker.offset);
        self.marker.offset = offset;
        self.marker.pos += 1;
        (self.marker.pos, token)
    }

    pub(crate) fn last_pos(&self) -> usize {
        self.marker.pos
    }

    pub(crate) fn slice(&self, range: Range<Marker<In>>) -> &'a In::Slice
    where
        In: SliceInput,
    {
        self.input.slice(range.start.offset..range.end.offset)
    }

    pub(crate) fn slice_from(&self, from: RangeFrom<Marker<In>>) -> &'a In::Slice
    where
        In: SliceInput,
    {
        self.input.slice_from(from.start.offset..)
    }

    pub(crate) fn slice_trailing(&self) -> &'a In::Slice
    where
        In: SliceInput,
    {
        self.input.slice_from(self.marker.offset..)
    }

    pub(crate) fn span_since(&self, before: Marker<In>) -> In::Span {
        self.input.span(before.offset..self.marker.offset)
    }

    pub(crate) fn skip_bytes<C>(&mut self, skip: usize)
    where
        C: Char,
        In: StrInput<C>,
    {
        self.marker.offset += skip;
    }

    pub(crate) fn emit(&mut self, error: Err) {
        self.errors.push(error);
        self.marker.err_count += 1;
    }

    pub(crate) fn into_errs(self) -> Vec<Err> {
        self.errors
    }
}

/// Struct used in [`Parser::validate`] to collect user-emitted errors
pub struct Emitter<E> {
    emitted: Vec<E>,
}

impl<E> Emitter<E> {
    pub(crate) fn new() -> Emitter<E> {
        Emitter {
            emitted: Vec::new(),
        }
    }

    pub(crate) fn errors(self) -> Vec<E> {
        self.emitted
    }

    /// Emit a non-fatal error
    pub fn emit(&mut self, err: E) {
        self.emitted.push(err)
    }
}
