use super::*;
use std::ops::Range;

pub trait Span: Clone {
    type Context: Clone;
    type Offset: Clone + Ord;

    fn new(context: Self::Context, range: Range<Self::Offset>) -> Self;
    fn range(&self) -> Range<Self::Offset>;
    fn start(&self) -> Self::Offset;
    fn end(&self) -> Self::Offset;
}

impl<T: Clone + Ord + fmt::Debug> Span for Range<Option<T>> {
    type Context = ();
    type Offset = Option<T>;

    fn new((): Self::Context, range: Self) -> Self { range }
    fn range(&self) -> Range<Self::Offset> { self.clone() }
    fn start(&self) -> Self::Offset { self.start.clone() }
    fn end(&self) -> Self::Offset { self.end.clone() }
}
