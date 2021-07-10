use super::*;

pub trait Stream<I> {
    fn peek(&mut self) -> Option<&I>;
    fn next(&mut self) -> Option<I>;

    // The number of tokens emitted by the stream so far
    fn position(&self) -> usize;
}

impl<'a, I> Stream<I> for &'a mut dyn Stream<I> {
    fn peek(&mut self) -> Option<&I> { (**self).peek() }
    fn next(&mut self) -> Option<I> { (**self).next() }
    fn position(&self) -> usize { (**self).position() }
}

pub struct IterStream<Iter: Iterator>(Peekable<Iter>, usize);

impl<Iter: Iterator> IterStream<Iter> {
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
