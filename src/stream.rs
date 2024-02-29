use super::*;

/// An input that dynamically pulls tokens from an [`Iterator`].
///
/// Internally, the stream will pull tokens in batches so as to avoid invoking the iterator every time a new token is
/// required.
pub struct Stream<I: Iterator> {
    tokens: Cell<(Vec<I::Item>, Option<I>)>,
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
            tokens: Cell::new((Vec::new(), Some(iter.into_iter()))),
        }
    }

    /// Box this stream, turning it into a [BoxedStream]. This can be useful in cases where your parser accepts input
    /// from several different sources and it needs to work with all of them.
    pub fn boxed<'a>(self) -> BoxedStream<'a, I::Item>
    where
        I: 'a,
    {
        let (vec, iter) = self.tokens.into_inner();
        Stream {
            tokens: Cell::new((vec, Some(Box::new(iter.expect("no iterator?!"))))),
        }
    }

    /// Like [`Stream::boxed`], but yields an [`BoxedExactSizeStream`], which implements [`ExactSizeInput`].
    pub fn exact_size_boxed<'a>(self) -> BoxedExactSizeStream<'a, I::Item>
    where
        I: ExactSizeIterator + 'a,
    {
        let (vec, iter) = self.tokens.into_inner();
        Stream {
            tokens: Cell::new((vec, Some(Box::new(iter.expect("no iterator?!"))))),
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
    type Offset = usize;
    type Token = I::Item;
    type Span = SimpleSpan<usize>;

    #[inline(always)]
    fn start(&self) -> Self::Offset {
        0
    }

    type TokenMaybe = I::Item;

    #[inline(always)]
    unsafe fn next_maybe(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::TokenMaybe>) {
        self.next(offset)
    }

    #[inline(always)]
    unsafe fn span(&self, range: Range<Self::Offset>) -> Self::Span {
        range.into()
    }

    #[inline]
    fn prev(offs: Self::Offset) -> Self::Offset {
        offs.saturating_sub(1)
    }
}

impl<'a, I: ExactSizeIterator + 'a> ExactSizeInput<'a> for Stream<I>
where
    I::Item: Clone,
{
    #[inline(always)]
    unsafe fn span_from(&self, range: RangeFrom<Self::Offset>) -> Self::Span {
        let mut other = Cell::new((Vec::new(), None));
        self.tokens.swap(&other);
        let len = other.get_mut().1.as_ref().expect("no iterator?!").len();
        self.tokens.swap(&other);
        (range.start..len).into()
    }
}

impl<'a, I: Iterator + 'a> ValueInput<'a> for Stream<I>
where
    I::Item: Clone,
{
    #[inline]
    unsafe fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) {
        let mut other = Cell::new((Vec::new(), None));
        self.tokens.swap(&other);

        let (vec, iter) = other.get_mut();

        // Pull new items into the vector if we need them
        if vec.len() <= offset {
            vec.extend(iter.as_mut().expect("no iterator?!").take(500));
        }

        // Get the token at the given offset
        let tok = vec.get(offset).cloned();

        self.tokens.swap(&other);

        (offset + tok.is_some() as usize, tok)
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
