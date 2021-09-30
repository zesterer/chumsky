use super::*;
use std::ops::Range;

pub trait Span: Clone {
    type Context: Clone;
    type Offset: Clone + Ord;

    fn new(context: Self::Context, range: Range<Option<Self::Offset>>) -> Self;
    fn range(&self) -> Range<Option<Self::Offset>>;
    fn start(&self) -> Option<Self::Offset>;
    fn end(&self) -> Option<Self::Offset>;
    fn display(&self) -> Box<dyn fmt::Display + '_>;
}

impl<T: Clone + Ord + fmt::Debug> Span for Range<Option<T>> {
    type Context = ();
    type Offset = T;

    fn new((): Self::Context, range: Self) -> Self { range }
    fn range(&self) -> Self { self.clone() }
    fn start(&self) -> Option<Self::Offset> { self.start.clone() }
    fn end(&self) -> Option<Self::Offset> { self.end.clone() }
    fn display(&self) -> Box<dyn fmt::Display + '_> { Box::new(format!("{:?}..{:?}", self.start, self.end)) }
}
