use super::*;

use std::ops::Range;

/// A trait implemented by token streams.
pub trait Stream<I, S: Span> {
    /// Peek at the next token and its span (if any), but do not progress the stream.
    fn peek(&mut self) -> Option<(&I, S)>;

    /// Peek at the next token (if any), but do not progress the stream.
    fn peek_token(&mut self) -> Option<&I> { self.peek().map(|(x, _)| x) }

    /// Peek at the span of the next token (if any), but do not progress the stream.
    fn peek_span(&mut self) -> Option<S> { self.peek().map(|(_, span)| span) }

    /// Returns the span of the last token to be pulled from the stream.
    fn last_span(&self) -> Option<S>;

    /// Progress the stream, returning the next token (if any).
    fn next(&mut self) -> Option<I>;
}

impl<'a, I, S: Span> Stream<I, S> for &'a mut dyn Stream<I, S> {
    fn peek(&mut self) -> Option<(&I, S)> { (**self).peek() }
    fn peek_token(&mut self) -> Option<&I> { (**self).peek_token() }
    fn peek_span(&mut self) -> Option<S> { (**self).peek_span() }
    fn last_span(&self) -> Option<S> { (**self).last_span() }
    fn next(&mut self) -> Option<I> { (**self).next() }
}

/// A trait that describes types that can be turned into token streams (types that implement [`Stream`]).
pub trait IntoStream<I, S: Span> {
    /// The type of the stream that this type can be transformed into.
    type Stream: Stream<I, S>;

    /// Transform this value into a stream.
    fn into_stream(self) -> Self::Stream;
}

/// A stream that wraps an [`Iterator`].
pub struct IterStream<Iter: Iterator>(Peekable<Iter>, usize);

impl<Iter: Iterator> IterStream<Iter> {
    /// Create a new [`IterStream`] from an iterator.
    pub fn new(iter: Iter) -> Self {
        Self(iter.peekable(), 0)
    }
}

impl<Iter: Iterator> Stream<Iter::Item, Range<usize>> for IterStream<Iter> {
    fn peek(&mut self) -> Option<(&Iter::Item, Range<usize>)> {
        let span = self.1..self.1 + 1;
        self.0.peek().map(|x| (x, span))
    }
    fn last_span(&self) -> Option<Range<usize>> { self.1.checked_sub(1).map(|s| s..s + 1) }
    fn next(&mut self) -> Option<Iter::Item> {
        self.1 += 1;
        self.0.next()
    }
}

impl<Iter: Iterator> IntoStream<Iter::Item, Range<usize>> for IterStream<Iter> {
    type Stream = Self;
    fn into_stream(self) -> Self::Stream { self }
}

impl<'a> IntoStream<char, Range<usize>> for &'a str {
    type Stream = IterStream<std::str::Chars<'a>>;
    fn into_stream(self) -> Self::Stream { IterStream::new(self.chars()) }
}

impl<'a, I: Clone> IntoStream<I, Range<usize>> for &'a [I] {
    type Stream = IterStream<std::iter::Cloned<std::slice::Iter<'a, I>>>;
    fn into_stream(self) -> Self::Stream { IterStream::new(self.into_iter().cloned()) }
}

impl<I> IntoStream<I, Range<usize>> for Vec<I> {
    type Stream = IterStream<std::vec::IntoIter<I>>;
    fn into_stream(self) -> Self::Stream { IterStream::new(self.into_iter()) }
}

impl<I, const N: usize> IntoStream<I, Range<usize>> for [I; N] {
    type Stream = IterStream<std::array::IntoIter<I, N>>;
    fn into_stream(self) -> Self::Stream { IterStream::new(std::array::IntoIter::new(self)) }
}

// impl<Iter: Iterator> IntoStream<Iter::Item, Range<usize>> for Iter {
//     type Stream = IterStream<Iter>;
//     fn into_stream(self) -> Self::Stream { IterStream::new(self) }
// }

/// A stream that wraps an [`Iterator`] of token/span pairs.
pub struct SpannedIterStream<Iter: Iterator, S>(Peekable<Iter>, Option<S>);

impl<Iter: Iterator, S> SpannedIterStream<Iter, S> {
    /// Create a new [`SpannedIterStream`] from an iterator.
    pub fn new(iter: Iter) -> Self {
        Self(iter.peekable(), None)
    }
}

impl<Iter: Iterator<Item = (I, S)>, I, S: Span + Clone> Stream<I, S> for SpannedIterStream<Iter, S> {
    fn peek(&mut self) -> Option<(&I, S)> { self.0.peek().map(|(x, span)| (x, span.clone())) }
    fn last_span(&self) -> Option<S> { self.1.clone() }
    fn next(&mut self) -> Option<I> {
        self.1 = None;
        let (x, span) = self.0.next()?;
        self.1 = Some(span);
        Some(x)
    }
}

impl<'a, I: Clone, S: Span + Clone> IntoStream<I, S> for &'a [(I, S)] {
    type Stream = SpannedIterStream<std::iter::Cloned<std::slice::Iter<'a, (I, S)>>, S>;
    fn into_stream(self) -> Self::Stream { SpannedIterStream::new(self.into_iter().cloned()) }
}

impl<I, S: Span + Clone> IntoStream<I, S> for Vec<(I, S)> {
    type Stream = SpannedIterStream<std::vec::IntoIter<(I, S)>, S>;
    fn into_stream(self) -> Self::Stream { SpannedIterStream::new(self.into_iter()) }
}

impl<I, S: Span + Clone, const N: usize> IntoStream<I, S> for [(I, S); N] {
    type Stream = SpannedIterStream<std::array::IntoIter<(I, S), N>, S>;
    fn into_stream(self) -> Self::Stream { SpannedIterStream::new(std::array::IntoIter::new(self)) }
}
