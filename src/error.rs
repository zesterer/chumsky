use std::fmt;

/// A trait that describes parser error types.
pub trait Error<I>: Sized {
    /// The position of the token that the error occurred at.
    fn position(&self) -> usize;

    /// Create a new error describing a conflict between the expected token and that which was found in its place.
    ///
    /// Using a `None` as `expected` indicates that accepted tokens cannot be described with a token. Using a `None` as
    /// `found` indicates that the end of input was reached, but was not expected.
    fn expected_found(position: usize, expected: Option<I>, found: Option<I>) -> Self;

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

/// A simple default error type that provides minimal functionality.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Simple<I> {
    position: usize,
    expected: Vec<I>,
    found: Option<I>,
}

impl<I> Error<I> for Simple<I> {
    fn position(&self) -> usize { self.position }
    fn expected_found(position: usize, expected: Option<I>, found: Option<I>) -> Self {
        Self {
            position,
            expected: expected.into_iter().collect(),
            found,
        }
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
            [expected] => write!(f, " but '{}' was expected", expected)?,
            [_, ..] => write!(f, " but one of '{}' expected", self.expected
                .iter()
                .map(|expected| expected.to_string())
                .collect::<Vec<_>>()
                .join(", "))?,
        }

        Ok(())
    }
}
impl<I: fmt::Debug + fmt::Display> std::error::Error for Simple<I> {}
