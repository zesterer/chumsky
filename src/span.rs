use std::ops::Range;

/// A trait that describes a span over a particular range of inputs.
///
/// Spans typically consist of some context, such as the file they originated from, and a start/end offset. Spans are
/// permitted to overlap one-another. The end offset must always be greater than or equal to the end offset.
pub trait Span: Clone {
    /// The context that comes packaged with a span. This is usually some way to uniquely identity the source file that
    /// a span originated in. However, it has no inherent meaning to Chumsky and can be anything. [`Range<usize>`]'s
    /// implementation of [`Span`] simply has a context of `()`.
    type Context: Clone;

    /// A type representing a span's start or end offset. Typically, [`usize`] is used.
    type Offset: Clone;

    /// Create a new span given a context and an offset range.
    fn new(context: Self::Context, range: Range<Self::Offset>) -> Self;

    /// Return the span's context.
    fn context(&self) -> Self::Context;

    /// Return the start offset of the span.
    fn start(&self) -> Self::Offset;

    /// Return the end offset of the span.
    fn end(&self) -> Self::Offset;
}

impl<T: Clone + Ord> Span for Range<T> {
    type Context = ();
    type Offset = T;

    fn new((): Self::Context, range: Self) -> Self { range }
    fn context(&self) -> Self::Context {}
    fn start(&self) -> Self::Offset { self.start.clone() }
    fn end(&self) -> Self::Offset { self.end.clone() }
}

impl<S: Clone, T: Clone> Span for (S, Range<T>) {
    type Context = S;
    type Offset = T;

    fn new(context: Self::Context, range: Range<T>) -> Self { (context, range) }
    fn context(&self) -> Self::Context { self.0.clone() }
    fn start(&self) -> Self::Offset { self.1.start.clone() }
    fn end(&self) -> Self::Offset { self.1.end.clone() }
}
