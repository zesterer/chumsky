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
    /// implementation of [`Span`] simply uses `()` as its context.
    type Context;

    /// A type representing a span's start or end offset from the start of the input.
    ///
    /// Typically, [`usize`] is used.
    ///
    /// NOTE: Offsets have no inherently meaning to Chumsky and are not used to decide how to prioritize errors. This
    /// means that it's perfectly fine for tokens to have non-continuous spans that bear no relation to their actual
    /// location in the input stream. This is useful for languages with an AST-level macro system that need to
    /// correctly point to symbols in the macro input when producing errors.
    type Offset: Clone;

    /// Create a new span given a context and an offset range.
    fn new(context: Self::Context, range: Range<Self::Offset>) -> Self;

    /// Return the span's context.
    fn context(&self) -> Self::Context;

    /// Return the start offset of the span.
    fn start(&self) -> Self::Offset;

    /// Return the end offset of the span.
    fn end(&self) -> Self::Offset;

    /// Turn this span into a zero-width span that starts and ends at the end of the original.
    ///
    /// For example, an original span like `3..7` will result in a new span of `7..7`.
    fn to_end(&self) -> Self
    where
        Self: Sized,
    {
        Self::new(self.context(), self.end()..self.end())
    }

    /// Combine two assumed-contiguous spans together into a larger span that encompasses both (and anything between).
    ///
    /// For example, spans like `3..5` and `7..8` will result in a unioned span of `3..8`.
    ///
    /// The spans may overlap one-another, but the start offset must come before the end offset for each span (i.e:
    /// each span must be 'well-formed'). If this is not the case, the result is unspecified.
    ///
    /// # Panics
    ///
    /// Panics if the [`Self::Context`]s of both spans are not equal.
    fn union(&self, other: Self) -> Self
    where
        Self::Context: PartialEq + fmt::Debug,
        Self::Offset: Ord,
        Self: Sized,
    {
        assert_eq!(
            self.context(),
            other.context(),
            "tried to union two spans with different contexts"
        );
        Self::new(
            self.context(),
            self.start().min(other.start())..self.end().max(other.end()),
        )
    }
}

/// The most basic implementor of `Span` - akin to `Range`, but `Copy` since it's not also
/// an iterator. Also has a `Display` implementation
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct SimpleSpan<T = usize, C = ()> {
    /// The start offset of the span.
    pub start: T,
    /// The end (exclusive) offset of the span.
    pub end: T,
    /// The context of the span (usually some ID representing the file path the span relates to).
    pub context: C,
}

impl<T, C> SimpleSpan<T, C> {
    /// Convert this span into a [`std::ops::Range`].
    pub fn into_range(self) -> Range<T> {
        self.start..self.end
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

impl<T> From<SimpleSpan<T, ()>> for Range<T> {
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

impl<T, C> IntoIterator for SimpleSpan<T, C>
where
    Range<T>: Iterator<Item = T>,
{
    type IntoIter = Range<T>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        self.start..self.end
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
