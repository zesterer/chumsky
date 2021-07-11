use super::*;

/// A trait implemented by token streams.
pub trait Stream<I> {
    /// Peek at the next token (if any), but do not progress the stream.
    fn peek(&mut self) -> Option<&I>;

    /// Progress the stream, returning the next token (if any).
    fn next(&mut self) -> Option<I>;

    /// Returns the number of tokens emitted by this stream so far.
    fn position(&self) -> usize;
}

impl<'a, I> Stream<I> for &'a mut dyn Stream<I> {
    fn peek(&mut self) -> Option<&I> { (**self).peek() }
    fn next(&mut self) -> Option<I> { (**self).next() }
    fn position(&self) -> usize { (**self).position() }
}

/// A stream that wraps an [`Iterator`].
pub struct IterStream<Iter: Iterator>(Peekable<Iter>, usize);

impl<Iter: Iterator> IterStream<Iter> {
    /// Create a new [`IterStream`] from an iterator.
    pub fn new(iter: Iter) -> Self {
        Self(iter.peekable(), 0)
    }
}

impl<Iter: Iterator> Stream<Iter::Item> for IterStream<Iter> {
    fn peek(&mut self) -> Option<&Iter::Item> { self.0.peek() }
    fn next(&mut self) -> Option<Iter::Item> {
        self.1 += 1;
        self.0.next()
    }
    fn position(&self) -> usize { self.1 }
}
