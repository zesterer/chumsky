//! Types and traits related to spans.
//!
//! *“We demand rigidly defined areas of doubt and uncertainty!”*
//!
//! You can use the [`Span`] trait to connect up chumsky to your compiler's knowledge of the input source.

use core::ops::Range;

/// A trait that describes a span over a particular range of inputs.
///
/// Spans typically consist of some context, such as the file they originated from, and a start/end offset. Spans are
/// permitted to overlap one-another. The end offset must always be greater than or equal to the start offset.
///
/// Span is automatically implemented for [`Range<T>`] and [`(C, Range<T>)`].
pub trait Span: Clone {
    /// Extra context used in a span.
    ///
    /// This is usually some way to uniquely identity the source file that a span originated in such as the file's
    /// path, URL, etc.
    ///
    /// NOTE: Span contexts have no inherent meaning to Chumsky and can be anything. For example, [`Range<usize>`]'s
    /// implementation of [`Span`] simply uses [`()`] as its context.
    type Context: Clone;

    /// A type representing a span's start or end offset from the start of the input.
    ///
    /// Typically, [`usize`] is used.
    ///
    /// NOTE: Offsets have no inherently meaning to Chumsky and are not used to decide how to prioritise errors. This
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
}

impl<T: Clone + Ord> Span for Range<T> {
    type Context = ();
    type Offset = T;

    fn new((): Self::Context, range: Self) -> Self {
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

impl<C: Clone, T: Clone> Span for (C, Range<T>) {
    type Context = C;
    type Offset = T;

    fn new(context: Self::Context, range: Range<T>) -> Self {
        (context, range)
    }
    fn context(&self) -> Self::Context {
        self.0.clone()
    }
    fn start(&self) -> Self::Offset {
        self.1.start.clone()
    }
    fn end(&self) -> Self::Offset {
        self.1.end.clone()
    }
}
