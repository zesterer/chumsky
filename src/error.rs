use std::fmt;

/// A trait that describes parser error types.
pub trait Error<I>: Sized {
    /// The label used to describe tokens or a token pattern in error messages.
    ///
    /// Commonly, this type has a way to represent both *specific* tokens and groups of tokens just 'expressions' or
    /// 'statements'.
    type Pattern; // TODO: Default to = I;

    /// The position of the token that the error occurred at.
    fn position(&self) -> usize;

    /// Create a new error describing a conflict between the expected token and that which was found in its place.
    ///
    /// Using a `None` as `expected` indicates that accepted tokens cannot be described with a token. Using a `None` as
    /// `found` indicates that the end of input was reached, but was not expected.
    fn expected_found(position: usize, expected: Vec<I>, found: Option<I>) -> Self;

    /// Alter the error message to indicate that the given labelled pattern was expected.
    fn label_expected<L: Into<Self::Pattern>>(self, label: L) -> Self;

    /// Merge two errors together, combining their elements together.
    ///
    /// Note that when the errors originate from two different locations in the token stream (i.e: their
    /// [`Error::position`] differs), the error error with the latest position should be preferred. When merging
    /// errors, unresolvable differences should favour `self`.
    fn merge(self, other: Self) -> Self {
        if self.position() < other.position() {
            other
        } else {
            self
        }
    }
}

/// A simple default token pattern that allows describing tokens and token patterns in error messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimplePattern<I> {
    /// A pattern with the given name was expected.
    Named(&'static str),
    /// A specific token was expected.
    Token(I),
}

impl<I> From<&'static str> for SimplePattern<I> {
    fn from(s: &'static str) -> Self { Self::Named(s) }
}

impl<I: fmt::Display> fmt::Display for SimplePattern<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Named(s) => write!(f, "{}", s),
            Self::Token(x) => write!(f, "'{}'", x),
        }
    }
}

/// A simple default error type that provides minimal functionality.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Simple<I> {
    position: usize,
    expected: Vec<SimplePattern<I>>,
    found: Option<I>,
}

impl<I> Error<I> for Simple<I> {
    type Pattern = SimplePattern<I>;

    fn position(&self) -> usize { self.position }

    fn expected_found(position: usize, expected: Vec<I>, found: Option<I>) -> Self {
        Self {
            position,
            expected: expected
                .into_iter()
                .map(SimplePattern::Token)
                .collect(),
            found,
        }
    }

    fn label_expected<L: Into<Self::Pattern>>(mut self, label: L) -> Self {
        self.expected = vec![label.into()];
        self
    }

    fn merge(mut self, mut other: Self) -> Self {
        if self.position() < other.position() {
            other
        } else if self.position() > other.position() {
            self
        } else {
            self.expected.append(&mut other.expected);
            self
        }
    }
}

impl<I: fmt::Display> fmt::Display for Simple<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(found) = &self.found {
            write!(f, "found '{}' ", found)?;
        } else {
            write!(f, "the input ended ")?;
        }

        write!(f, "at {}", self.position)?;

        match self.expected.as_slice() {
            [] => write!(f, " but end of input was expected")?,
            [expected] => write!(f, " but {} was expected", expected)?,
            [_, ..] => write!(f, " but one of {} was expected", self.expected
                .iter()
                .map(|expected| expected.to_string())
                .collect::<Vec<_>>()
                .join(", "))?,
        }

        Ok(())
    }
}
impl<I: fmt::Debug + fmt::Display> std::error::Error for Simple<I> {}
