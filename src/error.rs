//! Error types, traits and utilities.
//!
//! *“I like the cover," he said. "Don't Panic. It's the first helpful or intelligible thing anybody's said to me all
//! day.”*
//!
//! You can implement the [`Error`] trait to create your own parser errors, or you can use one provided by the crate
//! like [`Simple`] or [`Cheap`].

use super::*;
use alloc::{format, string::ToString};
use core::hash::Hash;

#[cfg(not(feature = "std"))]
use hashbrown::HashSet;
#[cfg(feature = "std")]
use std::collections::HashSet;

// (ahash + std) => ahash
// (ahash)       => ahash
// (std)         => std
// ()            => ahash
#[cfg(any(feature = "ahash", not(feature = "std")))]
type RandomState = hashbrown::hash_map::DefaultHashBuilder;
#[cfg(all(not(feature = "ahash"), feature = "std"))]
type RandomState = std::collections::hash_map::RandomState;

/// A trait that describes parser error types.
///
/// If you have a custom error type in your compiler, or your needs are not sufficiently met by [`Simple`], you should
/// implement this trait. If your error type has 'extra' features that allow for more specific error messages, you can
/// use the [`Parser::map_err`] or [`Parser::try_map`] functions to take advantage of these inline within your parser.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// type Span = std::ops::Range<usize>;
///
/// // A custom error type
/// #[derive(Debug, PartialEq)]
/// enum MyError {
///     ExpectedFound(Span, Vec<Option<char>>, Option<char>),
///     NotADigit(Span, char),
/// }
///
/// impl chumsky::Error<char> for MyError {
///     type Span = Span;
///     type Label = ();
///
///     fn expected_input_found<Iter: IntoIterator<Item = Option<char>>>(
///         span: Span,
///         expected: Iter,
///         found: Option<char>,
///     ) -> Self {
///         Self::ExpectedFound(span, expected.into_iter().collect(), found)
///     }
///
///     fn with_label(mut self, label: Self::Label) -> Self { self }
///
///     fn merge(mut self, mut other: Self) -> Self {
///         if let (Self::ExpectedFound(_, expected, _), Self::ExpectedFound(_, expected_other, _)) = (
///             &mut self,
///             &mut other,
///         ) {
///             expected.append(expected_other);
///         }
///         self
///     }
/// }
///
/// let numeral = filter_map(|span, c: char| match c.to_digit(10) {
///     Some(x) => Ok(x),
///     None => Err(MyError::NotADigit(span, c)),
/// });
///
/// assert_eq!(numeral.parse("3"), Ok(3));
/// assert_eq!(numeral.parse("7"), Ok(7));
/// assert_eq!(numeral.parse("f"), Err(vec![MyError::NotADigit(0..1, 'f')]));
/// ```
pub trait Error<I>: Sized {
    /// The type of spans to be used in the error.
    type Span: Span; // TODO: Default to = Range<usize>;

    /// The label used to describe a syntactic structure currently being parsed.
    ///
    /// This can be used to generate errors that tell the user what syntactic structure was currently being parsed when
    /// the error occurred.
    type Label; // TODO: Default to = &'static str;

    /// Create a new error describing a conflict between expected inputs and that which was actually found.
    ///
    /// `found` having the value `None` indicates that the end of input was reached, but was not expected.
    ///
    /// An expected input having the value `None` indicates that the end of input was expected.
    fn expected_input_found<Iter: IntoIterator<Item = Option<I>>>(
        span: Self::Span,
        expected: Iter,
        found: Option<I>,
    ) -> Self;

    /// Create a new error describing a delimiter that was not correctly closed.
    ///
    /// Provided to this function is the span of the unclosed delimiter, the delimiter itself, the span of the input
    /// that was found in its place, the closing delimiter that was expected but not found, and the input that was
    /// found in its place.
    ///
    /// The default implementation of this function uses [`Error::expected_input_found`], but you'll probably want to
    /// implement it yourself to take full advantage of the extra diagnostic information.
    fn unclosed_delimiter(
        unclosed_span: Self::Span,
        unclosed: I,
        span: Self::Span,
        expected: I,
        found: Option<I>,
    ) -> Self {
        #![allow(unused_variables)]
        Self::expected_input_found(span, Some(Some(expected)), found)
    }

    /// Indicate that the error occurred while parsing a particular syntactic structure.
    ///
    /// How the error handles this information is up to it. It can append it to a list of structures to get a sort of
    /// 'parse backtrace', or it can just keep only the most recent label. If the latter, this method should have no
    /// effect when the error already has a label.
    fn with_label(self, label: Self::Label) -> Self;

    /// Merge two errors that point to the same input together, combining their information.
    fn merge(self, other: Self) -> Self;
}

// /// A simple default input pattern that allows describing inputs and input patterns in error messages.
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

/// A type representing possible reasons for an error.
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
    /// An error with a custom message occurred.
    Custom(String),
}

impl<I: fmt::Display, S: fmt::Display> fmt::Display for SimpleReason<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        const DEFAULT_DISPLAY_UNEXPECTED: &str = "unexpected input";

        match self {
            Self::Unexpected => write!(f, "{}", DEFAULT_DISPLAY_UNEXPECTED),
            Self::Unclosed { span, delimiter } => {
                write!(f, "unclosed delimiter ({}) in {}", span, delimiter)
            }
            Self::Custom(string) => write!(f, "error {}", string),
        }
    }
}

/// A type representing zero, one, or many labels applied to an error
#[derive(Clone, Copy, Debug, PartialEq)]
enum SimpleLabel {
    Some(&'static str),
    None,
    Multi,
}

impl SimpleLabel {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (SimpleLabel::Some(a), SimpleLabel::Some(b)) if a == b => SimpleLabel::Some(a),
            (SimpleLabel::Some(_), SimpleLabel::Some(_)) => SimpleLabel::Multi,
            (SimpleLabel::Multi, _) => SimpleLabel::Multi,
            (_, SimpleLabel::Multi) => SimpleLabel::Multi,
            (SimpleLabel::None, x) => x,
            (x, SimpleLabel::None) => x,
        }
    }
}

impl From<SimpleLabel> for Option<&'static str> {
    fn from(label: SimpleLabel) -> Self {
        match label {
            SimpleLabel::Some(s) => Some(s),
            _ => None,
        }
    }
}

/// A simple default error type that tracks error spans, expected inputs, and the actual input found at an error site.
///
/// Please note that it uses a [`HashSet`] to remember expected symbols. If you find this to be too slow, you can
/// implement [`Error`] for your own error type or use [`Cheap`] instead.
#[derive(Clone, Debug)]
pub struct Simple<I: Hash + Eq, S = Range<usize>> {
    span: S,
    reason: SimpleReason<I, S>,
    expected: HashSet<Option<I>, RandomState>,
    found: Option<I>,
    label: SimpleLabel,
}

impl<I: Hash + Eq, S: Clone> Simple<I, S> {
    /// Create an error with a custom error message.
    pub fn custom<M: ToString>(span: S, msg: M) -> Self {
        Self {
            span,
            reason: SimpleReason::Custom(msg.to_string()),
            expected: HashSet::default(),
            found: None,
            label: SimpleLabel::None,
        }
    }

    /// Returns the span that the error occurred at.
    pub fn span(&self) -> S {
        self.span.clone()
    }

    /// Returns an iterator over possible expected patterns.
    pub fn expected(&self) -> impl ExactSizeIterator<Item = &Option<I>> + '_ {
        self.expected.iter()
    }

    /// Returns the input, if any, that was found instead of an expected pattern.
    pub fn found(&self) -> Option<&I> {
        self.found.as_ref()
    }

    /// Returns the reason for the error.
    pub fn reason(&self) -> &SimpleReason<I, S> {
        &self.reason
    }

    /// Returns the error's label, if any.
    pub fn label(&self) -> Option<&'static str> {
        self.label.into()
    }

    /// Map the error's inputs using the given function.
    ///
    /// This can be used to unify the errors between parsing stages that operate upon two forms of input (for example,
    /// the initial lexing stage and the parsing stage in most compilers).
    pub fn map<U: Hash + Eq, F: FnMut(I) -> U>(self, mut f: F) -> Simple<U, S> {
        Simple {
            span: self.span,
            reason: match self.reason {
                SimpleReason::Unclosed { span, delimiter } => SimpleReason::Unclosed {
                    span,
                    delimiter: f(delimiter),
                },
                SimpleReason::Unexpected => SimpleReason::Unexpected,
                SimpleReason::Custom(msg) => SimpleReason::Custom(msg),
            },
            expected: self.expected.into_iter().map(|e| e.map(&mut f)).collect(),
            found: self.found.map(f),
            label: self.label,
        }
    }
}

impl<I: Hash + Eq, S: Span + Clone + fmt::Debug> Error<I> for Simple<I, S> {
    type Span = S;
    type Label = &'static str;

    fn expected_input_found<Iter: IntoIterator<Item = Option<I>>>(
        span: Self::Span,
        expected: Iter,
        found: Option<I>,
    ) -> Self {
        Self {
            span,
            reason: SimpleReason::Unexpected,
            expected: expected.into_iter().collect(),
            found,
            label: SimpleLabel::None,
        }
    }

    fn unclosed_delimiter(
        unclosed_span: Self::Span,
        delimiter: I,
        span: Self::Span,
        expected: I,
        found: Option<I>,
    ) -> Self {
        Self {
            span,
            reason: SimpleReason::Unclosed {
                span: unclosed_span,
                delimiter,
            },
            expected: core::iter::once(Some(expected)).collect(),
            found,
            label: SimpleLabel::None,
        }
    }

    fn with_label(mut self, label: Self::Label) -> Self {
        match self.label {
            SimpleLabel::Some(_) => {}
            _ => {
                self.label = SimpleLabel::Some(label);
            }
        }
        self
    }

    fn merge(mut self, other: Self) -> Self {
        // TODO: Assert that `self.span == other.span` here?
        self.reason = match (&self.reason, &other.reason) {
            (SimpleReason::Unclosed { .. }, _) => self.reason,
            (_, SimpleReason::Unclosed { .. }) => other.reason,
            _ => self.reason,
        };
        self.label = self.label.merge(other.label);
        for expected in other.expected {
            self.expected.insert(expected);
        }
        self
    }
}

impl<I: Hash + Eq, S: PartialEq> PartialEq for Simple<I, S> {
    fn eq(&self, other: &Self) -> bool {
        self.span == other.span
            && self.found == other.found
            && self.reason == other.reason
            && self.label == other.label
    }
}

impl<I: Hash + Eq, S: Eq> Eq for Simple<I, S> {}

impl<I: fmt::Display + Hash + Eq, S: Span> fmt::Display for Simple<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO: Take `self.reason` into account

        if let Some(found) = &self.found {
            write!(f, "found {:?}", found.to_string())?;
        } else {
            write!(f, "found end of input")?;
        };

        match self.expected.len() {
            0 => {} //write!(f, " but end of input was expected")?,
            1 => write!(
                f,
                " but expected {}",
                match self.expected.iter().next().unwrap() {
                    Some(x) => format!("{:?}", x.to_string()),
                    None => "end of input".to_string(),
                },
            )?,
            _ => {
                write!(
                    f,
                    " but expected one of {}",
                    self.expected
                        .iter()
                        .map(|expected| match expected {
                            Some(x) => format!("{:?}", x.to_string()),
                            None => "end of input".to_string(),
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
            }
        }

        Ok(())
    }
}

#[cfg(feature = "std")]
impl<I: fmt::Debug + fmt::Display + Hash + Eq, S: Span + fmt::Display + fmt::Debug>
    std::error::Error for Simple<I, S>
{
}

/// A minimal error type that tracks only the error span and label. This type is most useful when you want fast parsing
/// but do not particularly care about the quality of error messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cheap<I, S = Range<usize>> {
    span: S,
    label: Option<&'static str>,
    phantom: PhantomData<I>,
}

impl<I, S: Clone> Cheap<I, S> {
    /// Returns the span that the error occurred at.
    pub fn span(&self) -> S {
        self.span.clone()
    }

    /// Returns the error's label, if any.
    pub fn label(&self) -> Option<&'static str> {
        self.label
    }
}

impl<I, S: Span + Clone + fmt::Debug> Error<I> for Cheap<I, S> {
    type Span = S;
    type Label = &'static str;

    fn expected_input_found<Iter: IntoIterator<Item = Option<I>>>(
        span: Self::Span,
        _: Iter,
        _: Option<I>,
    ) -> Self {
        Self {
            span,
            label: None,
            phantom: PhantomData,
        }
    }

    fn with_label(mut self, label: Self::Label) -> Self {
        self.label.get_or_insert(label);
        self
    }

    fn merge(self, _: Self) -> Self {
        self
    }
}

/// An internal type used to facilitate error prioritisation. You shouldn't need to interact with this type during
/// normal use of the crate.
pub struct Located<I, E> {
    pub(crate) at: usize,
    pub(crate) error: E,
    pub(crate) phantom: PhantomData<I>,
}

impl<I, E: Error<I>> Located<I, E> {
    /// Create a new [`Located`] with the give input position and error.
    pub fn at(at: usize, error: E) -> Self {
        Self {
            at,
            error,
            phantom: PhantomData,
        }
    }

    /// Get the maximum of two located errors. If they hold the same position in the input, merge them.
    pub fn max(self, other: impl Into<Option<Self>>) -> Self {
        let other = match other.into() {
            Some(other) => other,
            None => return self,
        };
        match self.at.cmp(&other.at) {
            Ordering::Greater => self,
            Ordering::Less => other,
            Ordering::Equal => Self {
                error: self.error.merge(other.error),
                ..self
            },
        }
    }

    /// Map the error with the given function.
    pub fn map<U, F: FnOnce(E) -> U>(self, f: F) -> Located<I, U> {
        Located {
            at: self.at,
            error: f(self.error),
            phantom: PhantomData,
        }
    }
}

// Merge two alternative errors
pub(crate) fn merge_alts<I, E: Error<I>, T: IntoIterator<Item = Located<I, E>>>(
    mut error: Option<Located<I, E>>,
    errors: T,
) -> Option<Located<I, E>> {
    for other in errors {
        match (error, other) {
            (Some(a), b) => {
                error = Some(b.max(a));
            }
            (None, b) => {
                error = Some(b);
            }
        }
    }
    error
}
