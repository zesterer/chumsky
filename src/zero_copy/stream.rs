use super::*;

use core::cell::Cell;

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
    /// # use chumsky::zero_copy::{prelude::*, input::Stream};
    /// let stream = Stream::from_iter((0..10).map(|i| char::from_digit(i, 10).unwrap()));
    ///
    /// let parser = text::digits::<_, _, extra::Err<Simple<_>>>(10).collect::<String>();
    ///
    /// assert_eq!(parser.parse(&stream).into_result().as_deref(), Ok("0123456789"));
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
}

/// A stream containing a boxed iterator. See [`Stream::boxed`].
pub type BoxedStream<'a, T> = Stream<Box<dyn Iterator<Item = T> + 'a>>;

impl<'a, I: Iterator> Input<'a> for &'a Stream<I>
where
    I::Item: Clone,
{
    type Offset = usize;
    type Token = I::Item;
    type Span = SimpleSpan<usize>;

    fn start(&self) -> Self::Offset {
        0
    }

    unsafe fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) {
        let mut other = Cell::new((Vec::new(), None));
        self.tokens.swap(&other);

        let (vec, iter) = other.get_mut();

        // Pull new items into the vector if we need them
        if vec.len() <= offset {
            vec.extend(iter.as_mut().expect("no iterator?!").take(500));
        }

        // Get the token at the given offset
        let tok = if let Some(tok) = vec.get(offset) {
            Some(tok.clone())
        } else {
            None
        };

        self.tokens.swap(&other);

        (offset + 1, tok)
    }

    unsafe fn span(&self, range: Range<Self::Offset>) -> Self::Span {
        range.into()
    }

    fn reborrow(&self) -> Self {
        *self
    }
}
