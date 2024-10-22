use super::*;

/// An input that dynamically pulls tokens from an [`Iterator`].
///
/// Internally, the stream will pull tokens in batches so as to avoid invoking the iterator every time a new token is
/// required.
pub struct Stream<I: Iterator> {
    tokens: Vec<I::Item>,
    iter: I,
}

impl<I: Iterator> Stream<I> {
    /// Create a new stream from an [`Iterator`].
    ///
    /// # Example
    ///
    /// ```
    /// # use chumsky::{prelude::*, input::Stream};
    /// let stream = Stream::from_iter((0..10).map(|i| char::from_digit(i, 10).unwrap()));
    ///
    /// let parser = text::digits::<_, _, extra::Err<Simple<_>>>(10).collect::<String>();
    ///
    /// assert_eq!(parser.parse(stream).into_result().as_deref(), Ok("0123456789"));
    /// ```
    pub fn from_iter<J: IntoIterator<IntoIter = I>>(iter: J) -> Self {
        Self {
            tokens: Vec::new(),
            iter: iter.into_iter(),
        }
    }

    /// Box this stream, turning it into a [BoxedStream]. This can be useful in cases where your parser accepts input
    /// from several different sources and it needs to work with all of them.
    pub fn boxed<'a>(self) -> BoxedStream<'a, I::Item>
    where
        I: 'a,
    {
        Stream {
            tokens: self.tokens,
            iter: Box::new(self.iter),
        }
    }

    /// Like [`Stream::boxed`], but yields an [`BoxedExactSizeStream`], which implements [`ExactSizeInput`].
    pub fn exact_size_boxed<'a>(self) -> BoxedExactSizeStream<'a, I::Item>
    where
        I: ExactSizeIterator + 'a,
    {
        Stream {
            tokens: self.tokens,
            iter: Box::new(self.iter),
        }
    }
}

/// A stream containing a boxed iterator. See [`Stream::boxed`].
pub type BoxedStream<'a, T> = Stream<Box<dyn Iterator<Item = T> + 'a>>;

/// A stream containing a boxed exact-sized iterator. See [`Stream::exact_size_boxed`].
pub type BoxedExactSizeStream<'a, T> = Stream<Box<dyn ExactSizeIterator<Item = T> + 'a>>;

impl<I: Iterator> Sealed for Stream<I> {}
impl<'a, I: Iterator + 'a> Input<'a> for Stream<I>
where
    I::Item: Clone,
{
    type Span = SimpleSpan<usize>;

    type Token = I::Item;
    type MaybeToken = I::Item;

    type Cursor = usize;

    type Cache = Self;

    #[inline(always)]
    fn begin(self) -> (Self::Cursor, Self::Cache) {
        (0, self)
    }

    #[inline]
    fn cursor_location(cursor: &Self::Cursor) -> usize {
        *cursor
    }

    #[inline(always)]
    unsafe fn next_maybe(
        this: &mut Self::Cache,
        cursor: &mut Self::Cursor,
    ) -> Option<Self::MaybeToken> {
        Self::next(this, cursor)
    }

    #[inline(always)]
    unsafe fn span(_this: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Span {
        (*range.start..*range.end).into()
    }
}

impl<'a, I: ExactSizeIterator + 'a> ExactSizeInput<'a> for Stream<I>
where
    I::Item: Clone,
{
    #[inline(always)]
    unsafe fn span_from(this: &mut Self::Cache, range: RangeFrom<&Self::Cursor>) -> Self::Span {
        (*range.start..this.tokens.len() + this.iter.len()).into()
    }
}

impl<'a, I: Iterator + 'a> ValueInput<'a> for Stream<I>
where
    I::Item: Clone,
{
    #[inline]
    unsafe fn next(this: &mut Self::Cache, cursor: &mut Self::Cursor) -> Option<Self::Token> {
        // Pull new items into the vector if we need them
        if this.tokens.len() <= *cursor {
            this.tokens.extend((&mut this.iter).take(512));
        }

        // Get the token at the given cursor
        this.tokens.get(*cursor).map(|tok| {
            *cursor += 1;
            tok.clone()
        })
    }
}

/// An input type that uses an iterator to generate tokens.
///
/// This input type supports backtracking by duplicating the iterator. It is recommended that your iterator is very
/// cheap to copy/clone.
pub struct IterInput<I, S> {
    iter: I,
    eoi: S,
}

impl<I, S> IterInput<I, S> {
    /// Create a new [`IterInput`] with the given iterator, and end of input span.
    pub fn new(iter: I, eoi: S) -> Self {
        Self { iter, eoi }
    }
}

impl<'src, I, T: 'src, S> Input<'src> for IterInput<I, S>
where
    I: Iterator<Item = (T, S)> + Clone + 'src,
    S: Span + 'src,
{
    type Cursor = (I, usize, Option<S::Offset>);
    type Span = S;

    type Token = T;
    type MaybeToken = T;

    type Cache = S; // eoi

    #[inline]
    fn begin(self) -> (Self::Cursor, Self::Cache) {
        ((self.iter, 0, None), self.eoi)
    }

    #[inline]
    fn cursor_location(cursor: &Self::Cursor) -> usize {
        cursor.1
    }

    unsafe fn next_maybe(
        _eoi: &mut Self::Cache,
        cursor: &mut Self::Cursor,
    ) -> Option<Self::MaybeToken> {
        cursor.0.next().map(|(tok, span)| {
            cursor.1 += 1;
            cursor.2 = Some(span.end());
            tok
        })
    }

    unsafe fn span(eoi: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Span {
        let start = range
            .start
            .0
            .clone()
            .next()
            .map(|(_, s)| s.start())
            .unwrap_or_else(|| eoi.start());
        let end = range.end.2.clone().unwrap_or_else(|| eoi.end());
        S::new(eoi.context(), start..end)
    }
}

#[test]
fn spanned() {
    fn parser<'a>() -> impl Parser<
        'a,
        input::SpannedInput<char, Range<usize>, BoxedStream<'static, (char, Range<usize>)>>,
        char,
    > {
        just('h')
    }

    let stream = Stream::from_iter(core::iter::once(('h', 0..1))).boxed();
    let stream = stream.spanned(0..10);

    assert_eq!(parser().parse(stream).into_result(), Ok('h'));
}
