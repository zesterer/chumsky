//! Error types, traits and utilities.
//!
//! *“I like the cover," he said. "Don't Panic. It's the first helpful or intelligible thing anybody's said to me all
//! day.”*
//!
//! You can implement the [`Error`] trait to create your own parser errors, or you can use one provided by the crate
//! like [`Simple`] or [`Rich`].

use super::*;

/// A trait that describes parser error types.
///
/// If you have a custom error type in your compiler, or your needs are not sufficiently met by [`Simple`], you should
/// implement this trait. If your error type has 'extra' features that allow for more specific error messages, you can
/// use the [`Parser::map_err`] or [`Parser::try_map`] functions to take advantage of these inline within your parser.
///
/// # Examples
///
/// ```
/// # use chumsky::zero_copy::{prelude::*, error::Simple};
/// type Span = std::ops::Range<usize>;
///
/// // A custom error type
/// #[derive(Debug, PartialEq)]
/// enum MyError {
///     ExpectedFound(Span, Vec<Option<char>>, Option<char>),
///     NotADigit(Span, char),
/// }
///
/// impl chumsky::zero_copy::error::Error<str> for MyError {
///     fn expected_found<Iter: IntoIterator<Item = Option<char>>>(
///         expected: Iter,
///         found: Option<char>,
///         span: Span,
///     ) -> Self {
///         Self::ExpectedFound(span, expected.into_iter().collect(), found)
///     }
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
/// let numeral = any::<_, _, ()>().try_map(|c: char, span| match c.to_digit(10) {
///     Some(x) => Ok(x),
///     None => Err(MyError::NotADigit(span, c)),
/// });
///
/// assert_eq!(numeral.parse("3").0, Some(3));
/// assert_eq!(numeral.parse("7").0, Some(7));
/// assert_eq!(numeral.parse("f").1, vec![MyError::NotADigit(0..1, 'f')]);
/// ```
pub trait Error<I: Input + ?Sized>: Sized {
    /// Create a new error describing a conflict between expected inputs and that which was actually found.
    ///
    /// `found` having the value `None` indicates that the end of input was reached, but was not expected.
    ///
    /// An expected input having the value `None` indicates that the end of input was expected.
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        expected: E,
        found: Option<I::Token>,
        span: I::Span,
    ) -> Self;

    /// Merge two errors that point to the same input together, combining their information.
    fn merge(self, other: Self) -> Self {
        #![allow(unused_variables)]
        self
    }
}

impl<I: Input + ?Sized> Error<I> for () {
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        _: E,
        _: Option<I::Token>,
        _: I::Span,
    ) -> Self {
    }
}

/// A minimal error type that tracks only the error span and found token. This type is most useful
/// when you want fast parsing but do not particularly care about the quality of error messages.
pub struct Simple<I: Input + ?Sized> {
    span: I::Span,
    found: Option<I::Token>,
}

impl<I: Input + ?Sized> Error<I> for Simple<I> {
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        _expected: E,
        found: Option<I::Token>,
        span: I::Span,
    ) -> Self {
        Self { span, found }
    }
}

impl<I: Input + ?Sized> fmt::Debug for Simple<I>
where
    I::Span: fmt::Debug,
    I::Token: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "found ")?;
        write_token_debug(f, &self.found)?;
        write!(f, " at {:?}", self.span)?;
        Ok(())
    }
}

/// A rich default error type that tracks error spans, expected inputs, and the actual input found at an error site.
///
/// Please note that it uses a [`Vec`] to remember expected symbols. If you find this to be too slow, you can
/// implement [`Error`] for your own error type or use [`Simple`] instead.
pub struct Rich<I: Input + ?Sized> {
    span: I::Span,
    expected: Vec<Option<I::Token>>,
    found: Option<I::Token>,
}

impl<I: Input + ?Sized> Error<I> for Rich<I>
where
    I::Token: PartialEq,
{
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        expected: E,
        found: Option<I::Token>,
        span: I::Span,
    ) -> Self {
        Self {
            span,
            expected: expected.into_iter().collect(),
            found,
        }
    }

    fn merge(mut self, other: Self) -> Self {
        for expected in other.expected {
            if !self.expected.contains(&expected) {
                self.expected.push(expected);
            }
        }
        self
    }
}

impl<I: Input + ?Sized> fmt::Debug for Rich<I>
where
    I::Span: fmt::Debug,
    I::Token: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "found ")?;
        write_token_debug(f, &self.found)?;
        write!(f, " at {:?}, expected ", self.span)?;
        match &self.expected[..] {
            [] => write!(f, "something else")?,
            [expected] => write_token_debug(f, expected)?,
            _ => {
                write!(f, "one of ")?;
                for expected in &self.expected[..self.expected.len() - 1] {
                    write_token_debug(f, expected)?;
                    write!(f, ", ")?;
                }
                write!(f, "or ")?;
                write_token_debug(f, self.expected.last().unwrap())?;
            }
        }
        Ok(())
    }
}

fn write_token_debug<T: fmt::Debug>(f: &mut fmt::Formatter, tok: &Option<T>) -> fmt::Result {
    match tok {
        Some(tok) => write!(f, "{:?}", tok),
        None => write!(f, "end of input"),
    }
}
