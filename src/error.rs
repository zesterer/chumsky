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
    type Label; // TODO: Default to = &'static str;

    /// The primary span that the error originated at, if one exists.
    fn span(&self) -> Self::Span;

    /// Create a new error describing a conflict between expected tokens and that which was actually found.
    ///
    /// Using a `None` as `found` indicates that the end of input was reached, but was not expected.
    fn expected_token_found<Iter: IntoIterator<Item = I>>(span: Self::Span, expected: Iter, found: Option<I>) -> Self;

    fn unclosed_delimiter(_start_span: Self::Span, _start: I, span: Self::Span, expected: I, found: Option<I>) -> Self {
        Self::expected_token_found(span, Some(expected), found)
    }

    /// Create a new error describing a conflict between an expected label and that the token that was actually found.
    ///
    /// Using a `None` as `found` indicates that the end of input was reached, but was not expected.
    // fn expected_label_found<L: Into<Self::Pattern>>(span: Self::Span, expected: L, found: Option<I>) -> Self {
    //     Self::expected_token_found(span, Vec::new(), found).into_labelled(expected)
    // }

    /// Indicate that the error occured while parsing a particular syntactic structure.
    fn with_label(self, label: Self::Label) -> Self;

    /// Merge two errors that point to the same token together, combining their information.
    fn merge(self, other: Self) -> Self;

    // fn debug(&self) -> &dyn fmt::Debug;
}

/// A simple default token pattern that allows describing tokens and token patterns in error messages.
// #[derive(Clone, Debug, PartialEq, Eq, Hash)]
// pub enum SimplePattern<I> {
//     /// A pattern with the given name was expected.
//     Labelled(&'static str),
//     /// A specific token was expected.
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimpleReason<I, S> {
    Unclosed(S, I),
}

/// A simple default error type that tracks error spans, expected patterns, and the token found at an error site.
#[derive(Clone, Debug)]
pub struct Simple<I: Hash, S = Range<usize>> {
    span: S,
    reason: Option<SimpleReason<I, S>>,
    expected: HashSet<I>,
    found: Option<I>,
    label: Option<&'static str>,
}

impl<I: Hash + Eq, S> Simple<I, S> {
    /// Returns an iterator over possible expected patterns.
    pub fn expected(&self) -> impl ExactSizeIterator<Item = &I> + '_ { self.expected.iter() }

    /// Returns the token, if any, that was found instead of an expected pattern.
    pub fn found(&self) -> Option<&I> { self.found.as_ref() }

    pub fn reason(&self) -> Option<&SimpleReason<I, S>> { self.reason.as_ref() }

    pub fn label(&self) -> Option<&'static str> { self.label }

    pub fn map<U: Hash + Eq, F: FnMut(I) -> U>(self, mut f: F) -> Simple<U, S> {
        Simple {
            span: self.span,
            reason: match self.reason {
                Some(SimpleReason::Unclosed(span, tok)) => Some(SimpleReason::Unclosed(span, f(tok))),
                None => None,
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

impl<I: fmt::Debug + Hash + Eq, S: Span + Clone + fmt::Debug> Error<I> for Simple<I, S> {
    type Span = S;
    type Label = &'static str;

    fn span(&self) -> Self::Span { self.span.clone() }

    fn expected_token_found<Iter: IntoIterator<Item = I>>(span: Self::Span, expected: Iter, found: Option<I>) -> Self {
        Self {
            span,
            reason: None,
            expected: expected
                .into_iter()
                .collect(),
            found,
            label: None,
        }
    }

    fn unclosed_delimiter(start_span: Self::Span, start: I, span: Self::Span, expected: I, found: Option<I>) -> Self {
        Self {
            span,
            reason: Some(SimpleReason::Unclosed(start_span, start)),
            expected: std::iter::once(expected).collect(),
            found,
            label: None,
        }
    }

    fn with_label(mut self, label: Self::Label) -> Self {
        self.label = Some(label);
        self
    }

    fn merge(mut self, other: Self) -> Self {
        // TODO: Assert that `self.span == other.span` here?
        self.reason = self.reason.or(other.reason);
        for expected in other.expected {
            self.expected.insert(expected);
        }
        self
    }

    // fn debug(&self) -> &dyn fmt::Debug { self }
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

/// A minimal error type that tracks only the error span.
#[derive(Clone, Debug)]
pub struct Cheap<I, S = Range<usize>> {
    span: S,
    label: Option<&'static str>,
    phantom: PhantomData<I>,
}

impl<I: fmt::Debug, S: Span + Clone + fmt::Debug> Error<I> for Cheap<I, S> {
    type Span = S;
    type Label = &'static str;

    fn span(&self) -> Self::Span { self.span.clone() }

    fn expected_token_found<Iter: IntoIterator<Item = I>>(span: Self::Span, _: Iter, _: Option<I>) -> Self {
        Self { span, label: None, phantom: PhantomData }
    }

    fn with_label(mut self, label: Self::Label) -> Self {
        self.label = Some(label);
        self
    }

    fn merge(self, _: Self) -> Self { self }

    // fn debug(&self) -> &dyn fmt::Debug { self }
}
