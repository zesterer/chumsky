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
/// type Span = SimpleSpan<usize>;
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
/// let numeral = any().try_map(|c: char, span| match c.to_digit(10) {
///     Some(x) => Ok(x),
///     None => Err(MyError::NotADigit(span, c)),
/// }).state::<()>().ctx::<()>();
///
/// assert_eq!(numeral.parse("3").into_result(), Ok(3));
/// assert_eq!(numeral.parse("7").into_result(), Ok(7));
/// assert_eq!(numeral.parse("f").into_errors(), vec![MyError::NotADigit((0..1).into(), 'f')]);
/// ```
pub trait Error<In: Input + ?Sized>: Sized {
    /// Create a new error describing a conflict between expected inputs and that which was actually found.
    ///
    /// `found` having the value `None` indicates that the end of input was reached, but was not expected.
    ///
    /// An expected input having the value `None` indicates that the end of input was expected.
    fn expected_found<Err: IntoIterator<Item = Option<In::Token>>>(
        expected: Err,
        found: Option<In::Token>,
        span: In::Span,
    ) -> Self;

    /// Merge two errors that point to the same input together, combining their information.
    fn merge(self, other: Self) -> Self {
        #![allow(unused_variables)]
        self
    }
}

/// A ZST error type that tracks only whether a parse error occurred at all. This type is for when
/// you want maximum parse speed, at the cost of all error reporting.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct EmptyErr(());

impl<In: Input + ?Sized> Error<In> for EmptyErr {
    fn expected_found<Err: IntoIterator<Item = Option<In::Token>>>(
        _: Err,
        _: Option<In::Token>,
        _: In::Span,
    ) -> Self {
        EmptyErr(())
    }
}

/// A minimal error type that tracks only the error span and found token. This type is most useful
/// when you want fast parsing but do not particularly care about the quality of error messages.
pub struct Simple<In: Input + ?Sized> {
    span: In::Span,
    found: Option<In::Token>,
}

impl<In: Input + ?Sized> Error<In> for Simple<In> {
    fn expected_found<Err: IntoIterator<Item = Option<In::Token>>>(
        _expected: Err,
        found: Option<In::Token>,
        span: In::Span,
    ) -> Self {
        Self { span, found }
    }
}

impl<In: Input + ?Sized> PartialEq for Simple<In>
where
    In::Token: PartialEq,
    In::Span: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.span == other.span && self.found == other.found
    }
}

impl<In: Input + ?Sized> fmt::Debug for Simple<In>
where
    In::Span: fmt::Debug,
    In::Token: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "found ")?;
        write_token(f, In::Token::fmt, &self.found)?;
        write!(f, " at {:?}", self.span)?;
        Ok(())
    }
}

// TODO: Maybe should make ExpectedFound encapsulated a bit more
/// The reason for a [`Rich`] error
pub enum RichReason<I: Input + ?Sized> {
    /// An unexpected input was found
    ExpectedFound {
        /// The tokens expected
        expected: Vec<Option<I::Token>>,
        /// The tokens found
        found: Option<I::Token>,
    },
    /// An error with a custom message
    Custom(String),
    /// Multiple unrelated reasons were merged
    Many(Vec<RichReason<I>>),
}

impl<I: Input + ?Sized> RichReason<I>
where
    I::Token: PartialEq,
{
    fn flat_merge(self, other: RichReason<I>) -> RichReason<I> {
        match (self, other) {
            (
                RichReason::ExpectedFound { expected: mut this_expected, found },
                RichReason::ExpectedFound { expected: other_expected, .. },
            ) => {
                for expected in other_expected {
                    if !this_expected.contains(&expected) {
                        this_expected.push(expected);
                    }
                }
                RichReason::ExpectedFound { expected: this_expected, found }
            }
            (RichReason::Many(mut m1), RichReason::Many(m2)) => {
                m1.extend(m2);
                RichReason::Many(m1)
            }
            (RichReason::Many(mut m), other) => {
                m.push(other);
                RichReason::Many(m)
            }
            (this, RichReason::Many(mut m)) => {
                m.push(this);
                RichReason::Many(m)
            }
            (this, other) => {
                RichReason::Many(vec![this, other])
            }
        }
    }
}

impl<I: Input + ?Sized> PartialEq for RichReason<I>
where
    I::Token: PartialEq,
    I::Span: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                RichReason::ExpectedFound { expected: e1, found: f1 },
                RichReason::ExpectedFound { expected: e2, found: f2 },
            ) => {
                f1 == f2 && e1 == e2
            }
            (
                RichReason::Custom(msg1),
                RichReason::Custom(msg2),
            ) => {
                msg1 == msg2
            }
            (
                RichReason::Many(m1),
                RichReason::Many(m2),
            ) => {
                m1 == m2
            }
            _ => false,
        }
    }
}

/// A rich default error type that tracks error spans, expected inputs, and the actual input found at an error site.
///
/// Please note that it uses a [`Vec`] to remember expected symbols. If you find this to be too slow, you can
/// implement [`Error`] for your own error type or use [`Simple`] instead.
pub struct Rich<In: Input + ?Sized> {
    span: In::Span,
    reason: RichReason<In>,
}

impl<In: Input + ?Sized> Rich<In> {
    fn inner_fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        token: fn(&In::Token, &mut fmt::Formatter<'_>) -> fmt::Result,
        span: fn(&In::Span, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        match &self.reason {
            RichReason::ExpectedFound {
                expected,
                found,
            } => {
                write!(f, "found ")?;
                write_token(f, token, &found)?;
                write!(f, " at ")?;
                span(&self.span, f)?;
                write!(f, "expected ")?;
                match &expected[..] {
                    [] => write!(f, "something else")?,
                    [expected] => write_token(f, token, expected)?,
                    _ => {
                        write!(f, "one of ")?;
                        for expected in &expected[..expected.len() - 1] {
                            write_token(f, token, expected)?;
                            write!(f, ", ")?;
                        }
                        write!(f, "or ")?;
                        write_token(f, token, expected.last().unwrap())?;
                    }
                }
            }
            RichReason::Custom(msg) => {
                write!(f, "{} at ", msg)?;
                span(&self.span, f)?;
            }
            RichReason::Many(_) => {
                write!(f, "Multiple errors found at ")?;
                span(&self.span, f)?;
            }
        }
        Ok(())
    }
}

impl<In: Input + ?Sized> Rich<In>
where
    In::Span: Clone,
    In::Token: Clone,
{
    /// Create an error with a custom message and span
    pub fn custom<M: ToString>(span: In::Span, msg: M) -> Rich<In> {
        Rich {
            span,
            reason: RichReason::Custom(msg.to_string()),
        }
    }

    /// Get the span associated with this error
    pub fn span(&self) -> In::Span {
        self.span.clone()
    }

    /// Get the reason fro this error
    pub fn reason(&self) -> &RichReason<In> {
        &self.reason
    }
}

impl<In: Input + ?Sized> Error<In> for Rich<In>
where
    In::Token: PartialEq,
{
    fn expected_found<Err: IntoIterator<Item = Option<In::Token>>>(
        expected: Err,
        found: Option<In::Token>,
        span: In::Span,
    ) -> Self {
        Self {
            span,
            reason: RichReason::ExpectedFound {
                expected: expected.into_iter().collect(),
                found,
            },
        }
    }

    fn merge(self, other: Self) -> Self {
        let new_reason = self.reason.flat_merge(other.reason);
        Self {
            span: self.span,
            reason: new_reason,
        }
    }
}

impl<I: Input + ?Sized> PartialEq for Rich<I>
where
    I::Token: PartialEq,
    I::Span: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.span == other.span && self.reason == other.reason
    }
}

impl<In: Input + ?Sized> fmt::Debug for Rich<In>
where
    In::Span: fmt::Debug,
    In::Token: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner_fmt(f, In::Token::fmt, In::Span::fmt)
    }
}

impl<In: Input + ?Sized> fmt::Display for Rich<In>
where
    In::Span: fmt::Display,
    In::Token: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner_fmt(f, In::Token::fmt, In::Span::fmt)
    }
}

fn write_token<T>(
    f: &mut fmt::Formatter,
    writer: fn(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
    tok: &Option<T>
) -> fmt::Result {
    match tok {
        Some(tok) => writer(tok, f),
        None => write!(f, "end of input"),
    }
}
