use super::*;
use std::{
    collections::HashSet,
    hash::Hash,
};

/// A trait that describes parser error types.
pub trait Error<I>: Sized {
    /// The type of spans to be used in the error.
    type Span: Span; // TODO: Default to = Range<usize>;

    /// The label used to describe a syntatic structure currently being parsed.
    ///
    /// This can be used to generate errors that tell the user what syntactic structure was currently being parsed when
    /// the error occured.
    type Label; // TODO: Default to = &'static str;

    /// Create a new error describing a conflict between expected inputs and that which was actually found.
    ///
    /// Using a `None` as `found` indicates that the end of input was reached, but was not expected.
    fn expected_input_found<Iter: IntoIterator<Item = I>>(span: Self::Span, expected: Iter, found: Option<I>) -> Self;

    /// Create a new error describing a delimiter that was not correctly closed.
    ///
    /// Provided to this function is the span of the unclosed delimiter, the delimiter itself, the span of the input
    /// that was found in its place, the closing delimiter that was expected but not found, and the input that was
    /// found in its place.
    fn unclosed_delimiter(_start_span: Self::Span, _start: I, span: Self::Span, expected: I, found: Option<I>) -> Self {
        Self::expected_input_found(span, Some(expected), found)
    }

    /// Indicate that the error occured while parsing a particular syntactic structure.
    ///
    /// How the error handles this information is up to it. It can append it to a list of structures to get a sort of
    /// 'parse backtrace', or it can just keep only the most recent label. If the latter, this method should have no
    /// effect when the error already has a label.
    fn with_label(self, label: Self::Label) -> Self;

    /// Merge two errors that point to the same input together, combining their information.
    fn merge(self, other: Self) -> Self;
}

/// A simple default input pattern that allows describing inputs and input patterns in error messages.
// #[derive(Clone, Debug, PartialEq, Eq, Hash)]
// pub enum SimplePattern<I> {
//     /// A pattern with the given name was expected.
//     Labelled(&'static str),
//     /// A specific input was expected.
//     Token(I),
// }

// impl<I> From<&'static str> for SimplePattern<I> {
//     fn from(s: &'static str) -> Self { Self::Labelled(s) }
// }

// impl<I: fmt::Display> fmt::Display for SimplePattern<I> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         match self {
//             Self::Labelled(s) => write!(f, "{}", s),
//             Self::Token(x) => write!(f, "'{}'", x),
//         }
//     }
// }

/// A type representing possible reasons for an error
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimpleReason<I, S> {
    /// An unexpected input was found.
    Unexpected,
    /// An unclosed delimiter was found.
    Unclosed {
        /// The span of the unclosed delimiter.
        span: S,
        /// The unclosed delimiter.
        delimiter: I,
    },
}

/// A simple default error type that tracks error spans, expected patterns, and the input found at an error site.
#[derive(Clone, Debug)]
pub struct Simple<I: Hash, S = Range<usize>> {
    span: S,
    reason: SimpleReason<I, S>,
    expected: HashSet<I>,
    found: Option<I>,
    label: Option<&'static str>,
}

impl<I: Hash + Eq, S: Clone> Simple<I, S> {
    /// Returns the span that the error occured at.
    pub fn span(&self) -> S { self.span.clone() }

    /// Returns an iterator over possible expected patterns.
    pub fn expected(&self) -> impl ExactSizeIterator<Item = &I> + '_ { self.expected.iter() }

    /// Returns the input, if any, that was found instead of an expected pattern.
    pub fn found(&self) -> Option<&I> { self.found.as_ref() }

    /// Returns the reason for the error.
    pub fn reason(&self) -> &SimpleReason<I, S> { &self.reason }

    /// Returns the error's label, if any.
    pub fn label(&self) -> Option<&'static str> { self.label }

    /// Map the error's inputs using the given function.
    ///
    /// This can be used to unify the errors between parsing stages that operate upon two forms of input (for example,
    /// the initial lexing stage and the parsing stage in most compilers).
    pub fn map<U: Hash + Eq, F: FnMut(I) -> U>(self, mut f: F) -> Simple<U, S> {
        Simple {
            span: self.span,
            reason: match self.reason {
                SimpleReason::Unclosed { span, delimiter } => SimpleReason::Unclosed {span, delimiter: f(delimiter) },
                SimpleReason::Unexpected => SimpleReason::Unexpected,
            },
            expected: self.expected
                .into_iter()
                .map(&mut f)
                .collect(),
            found: self.found.map(f),
            label: self.label,
        }
    }
}

impl<I: Hash + Eq, S: Span + Clone + fmt::Debug> Error<I> for Simple<I, S> {
    type Span = S;
    type Label = &'static str;

    fn expected_input_found<Iter: IntoIterator<Item = I>>(span: Self::Span, expected: Iter, found: Option<I>) -> Self {
        Self {
            span,
            reason: SimpleReason::Unexpected,
            expected: expected
                .into_iter()
                .collect(),
            found,
            label: None,
        }
    }

    fn unclosed_delimiter(start_span: Self::Span, delimiter: I, span: Self::Span, expected: I, found: Option<I>) -> Self {
        Self {
            span,
            reason: SimpleReason::Unclosed { span: start_span, delimiter },
            expected: std::iter::once(expected).collect(),
            found,
            label: None,
        }
    }

    fn with_label(mut self, label: Self::Label) -> Self {
        self.label.get_or_insert(label);
        self
    }

    fn merge(mut self, other: Self) -> Self {
        // TODO: Assert that `self.span == other.span` here?
        self.reason = match (&self.reason, &other.reason) {
            (SimpleReason::Unclosed { .. }, _) => self.reason,
            (_, SimpleReason::Unclosed { .. }) => other.reason,
            _ => self.reason,
        };
        for expected in other.expected {
            self.expected.insert(expected);
        }
        self
    }
}

impl<I: fmt::Display + Hash, S: Span + fmt::Display> fmt::Display for Simple<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(found) = &self.found {
            write!(f, "found '{}' ", found)?;
            write!(f, "at {} ", self.span)?;
        } else {
            write!(f, "the input ended ")?;
        }


        match self.expected.len() {
            0 => write!(f, "but end of input was expected")?,
            1 => write!(f, "but {} was expected", self.expected.iter().next().unwrap())?,
            _ => write!(f, "but one of {} was expected", self.expected
                .iter()
                .map(|expected| expected.to_string())
                .collect::<Vec<_>>()
                .join(", "))?,
        }

        Ok(())
    }
}

impl<I: fmt::Debug + fmt::Display + Hash, S: Span + fmt::Display + fmt::Debug> std::error::Error for Simple<I, S> {}

/// A minimal error type that tracks only the error span and label. This type is most useful when you want fast parsing
/// but do not particularly care about the quality of error messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cheap<I, S = Range<usize>> {
    span: S,
    label: Option<&'static str>,
    phantom: PhantomData<I>,
}

impl<I, S: Clone> Cheap<I, S> {
    /// Returns the span that the error occured at.
    pub fn span(&self) -> S { self.span.clone() }

    /// Returns the error's label, if any.
    pub fn label(&self) -> Option<&'static str> { self.label }
}

impl<I, S: Span + Clone + fmt::Debug> Error<I> for Cheap<I, S> {
    type Span = S;
    type Label = &'static str;

    fn expected_input_found<Iter: IntoIterator<Item = I>>(span: Self::Span, _: Iter, _: Option<I>) -> Self {
        Self { span, label: None, phantom: PhantomData }
    }

    fn with_label(mut self, label: Self::Label) -> Self {
        self.label.get_or_insert(label);
        self
    }

    fn merge(self, _: Self) -> Self { self }
}
