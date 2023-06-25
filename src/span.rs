//! Types and traits related to spans.
//!
//! *“We demand rigidly defined areas of doubt and uncertainty!”*
//!
//! You can use the [`Span`] trait to connect up chumsky to your compiler's knowledge of the input source.

use super::*;

/// A trait that describes a span over a particular range of inputs.
///
/// Spans typically consist of some context, such as the file they originated from, and a start/end offset. Spans are
/// permitted to overlap one-another. The end offset must always be greater than or equal to the start offset.
///
/// Span is automatically implemented for [`Range<T>`] and [`(C, Range<T>)`].
pub trait Span {
    /// Extra context used in a span.
    ///
    /// This is usually some way to uniquely identity the source file that a span originated in such as the file's
    /// path, URL, etc.
    ///
    /// NOTE: Span contexts have no inherent meaning to Chumsky and can be anything. For example, [`Range<usize>`]'s
    /// implementation of [`Span`] simply uses [`()`] as its context.
    type Context;

    /// A type representing a span's start or end offset from the start of the input.
    ///
    /// Typically, [`usize`] is used.
    ///
    /// NOTE: Offsets have no inherently meaning to Chumsky and are not used to decide how to prioritise errors. This
    /// means that it's perfectly fine for tokens to have non-continuous spans that bear no relation to their actual
    /// location in the input stream. This is useful for languages with an AST-level macro system that need to
    /// correctly point to symbols in the macro input when producing errors.
    type Offset;

    /// Create a new span given a context and an offset range.
    fn new(context: Self::Context, range: Range<Self::Offset>) -> Self;

    /// Return the span's context.
    fn context(&self) -> Self::Context;

    /// Return the start offset of the span.
    fn start(&self) -> Self::Offset;

    /// Return the end offset of the span.
    fn end(&self) -> Self::Offset;
}

/// The most basic implementor of `Span` - akin to `Range`, but `Copy` since it's not also
/// an iterator. Also has a `Display` implementation
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct SimpleSpan<T = usize, C = ()> {
    /// The start offset of the span.
    pub start: T,
    /// The end (exclusive) offset of the span.
    pub end: T,
    context: C,
}

impl<T> SimpleSpan<T> {
    /// Create a new `SimpleSpan` from a start and end offset
    pub fn new(start: T, end: T) -> SimpleSpan<T> {
        SimpleSpan {
            start,
            end,
            context: (),
        }
    }

    /// Create a new `SimpleSpan` from a single offset, useful for an EOI (End Of Input) span.
    pub fn splat(offset: T) -> SimpleSpan<T> {
        Self::new(offset, offset)
    }
    
    /// Convert this span into a [`std::ops::Range`].
    pub fn into_range(self) -> Range<T> {
        self.into()
    }
}

impl<T> From<Range<T>> for SimpleSpan<T> {
    fn from(range: Range<T>) -> Self {
        SimpleSpan {
            start: range.start,
            end: range.end,
            context: (),
        }
    }
}

impl<T> From<SimpleSpan<T>> for Range<T> {
    fn from(span: SimpleSpan<T>) -> Self {
        Range {
            start: span.start,
            end: span.end,
        }
    }
}

impl<T, C> fmt::Debug for SimpleSpan<T, C>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}..{:?}", self.start, self.end)
    }
}

impl<T, C> fmt::Display for SimpleSpan<T, C>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl<T> IntoIterator for SimpleSpan<T>
where
    Range<T>: Iterator<Item = T>,
{
    type IntoIter = Range<T>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        self.into()
    }
}

impl<T: Clone, C: Clone> Span for SimpleSpan<T, C> {
    type Context = C;
    type Offset = T;

    fn new(context: Self::Context, range: Range<Self::Offset>) -> Self {
        Self {
            start: range.start,
            end: range.end,
            context,
        }
    }
    fn context(&self) -> Self::Context {
        self.context.clone()
    }
    fn start(&self) -> Self::Offset {
        self.start.clone()
    }
    fn end(&self) -> Self::Offset {
        self.end.clone()
    }
}

impl<C: Clone, S: Span<Context = ()>> Span for (C, S) {
    type Context = C;
    type Offset = S::Offset;

    fn new(context: Self::Context, range: Range<Self::Offset>) -> Self {
        (context, S::new((), range))
    }
    fn context(&self) -> Self::Context {
        self.0.clone()
    }
    fn start(&self) -> Self::Offset {
        self.1.start()
    }
    fn end(&self) -> Self::Offset {
        self.1.end()
    }
}

impl<T: Clone> Span for Range<T> {
    type Context = ();
    type Offset = T;

    fn new(_context: Self::Context, range: Range<Self::Offset>) -> Self {
        range
    }
    fn context(&self) -> Self::Context {}
    fn start(&self) -> Self::Offset {
        self.start.clone()
    }
    fn end(&self) -> Self::Offset {
        self.end.clone()
    }
}
