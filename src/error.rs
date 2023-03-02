//! Error types, traits and utilities.
//!
//! *“I like the cover," he said. "Don't Panic. It's the first helpful or intelligible thing anybody's said to me all
//! day.”*
//!
//! You can implement the [`Error`] trait to create your own parser errors, or you can use one provided by the crate
//! like [`Simple`] or [`Rich`].

use super::*;
use alloc::string::ToString;

/// A trait that describes parser error types.
///
/// If you have a custom error type in your compiler, or your needs are not sufficiently met by [`Simple`], you should
/// implement this trait. If your error type has 'extra' features that allow for more specific error messages, you can
/// use the [`Parser::map_err`] or [`Parser::try_map`] functions to take advantage of these inline within your parser.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Simple};
/// type Span = SimpleSpan<usize>;
///
/// // A custom error type
/// #[derive(Debug, PartialEq)]
/// enum MyError {
///     ExpectedFound(Span, Vec<Option<char>>, Option<char>),
///     NotADigit(Span, char),
/// }
///
/// impl<'a> chumsky::error::Error<'a, &'a str> for MyError {
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
/// let numeral = any::<_, extra::Err<MyError>>().try_map(|c: char, span| match c.to_digit(10) {
///     Some(x) => Ok(x),
///     None => Err(MyError::NotADigit(span, c)),
/// });
///
/// assert_eq!(numeral.parse("3").into_result(), Ok(3));
/// assert_eq!(numeral.parse("7").into_result(), Ok(7));
/// assert_eq!(numeral.parse("f").into_errors(), vec![MyError::NotADigit((0..1).into(), 'f')]);
/// ```
pub trait Error<'a, I: Input<'a>>: Sized {
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

/// A ZST error type that tracks only whether a parse error occurred at all. This type is for when
/// you want maximum parse speed, at the cost of all error reporting.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Copy, Clone)]
pub struct EmptyErr(());

impl<'a, I: Input<'a>> Error<'a, I> for EmptyErr {
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        _: E,
        _: Option<I::Token>,
        _: I::Span,
    ) -> Self {
        EmptyErr(())
    }
}

impl fmt::Display for EmptyErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error")
    }
}

/// A minimal error type that tracks only the error span and found token. This type is most useful
/// when you want fast parsing but do not particularly care about the quality of error messages.
pub struct Simple<'a, I: Input<'a>> {
    span: I::Span,
    found: Option<I::Token>,
}

impl<'a, I: Input<'a>> Error<'a, I> for Simple<'a, I> {
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        _expected: E,
        found: Option<I::Token>,
        span: I::Span,
    ) -> Self {
        Self { span, found }
    }
}

impl<'a, I: Input<'a>> PartialEq for Simple<'a, I>
where
    I::Token: PartialEq,
    I::Span: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.span == other.span && self.found == other.found
    }
}

impl<'a, I: Input<'a>> fmt::Debug for Simple<'a, I>
where
    I::Span: fmt::Debug,
    I::Token: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "found ")?;
        write_token(f, I::Token::fmt, &self.found)?;
        write!(f, " at {:?}", self.span)?;
        Ok(())
    }
}

impl<'a, I: Input<'a>> fmt::Display for Simple<'a, I>
where
    I::Span: fmt::Debug,
    I::Token: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

// TODO: Maybe should make ExpectedFound encapsulated a bit more
/// The reason for a [`Rich`] error
pub enum RichReason<'a, I: Input<'a>> {
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
    Many(Vec<RichReason<'a, I>>),
}

impl<'a, I: Input<'a>> RichReason<'a, I> {
    fn found(&self) -> Option<&I::Token> {
        match self {
            RichReason::ExpectedFound { found, .. } => found.as_ref(),
            RichReason::Custom(_) => None,
            RichReason::Many(many) => many.iter().find_map(|r| r.found()),
        }
    }
}

impl<'a, I: Input<'a>> RichReason<'a, I>
where
    I::Token: PartialEq,
{
    fn flat_merge(self, other: Self) -> Self {
        match (self, other) {
            (
                RichReason::ExpectedFound {
                    expected: mut this_expected,
                    found,
                },
                RichReason::ExpectedFound {
                    expected: other_expected,
                    ..
                },
            ) => {
                for expected in other_expected {
                    if !this_expected.contains(&expected) {
                        this_expected.push(expected);
                    }
                }
                RichReason::ExpectedFound {
                    expected: this_expected,
                    found,
                }
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
            (this, other) => RichReason::Many(vec![this, other]),
        }
    }
}

impl<'a, I: Input<'a>> PartialEq for RichReason<'a, I>
where
    I::Token: PartialEq,
    I::Span: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                RichReason::ExpectedFound {
                    expected: e1,
                    found: f1,
                },
                RichReason::ExpectedFound {
                    expected: e2,
                    found: f2,
                },
            ) => f1 == f2 && e1 == e2,
            (RichReason::Custom(msg1), RichReason::Custom(msg2)) => msg1 == msg2,
            (RichReason::Many(m1), RichReason::Many(m2)) => m1 == m2,
            _ => false,
        }
    }
}

/// A rich default error type that tracks error spans, expected inputs, and the actual input found at an error site.
///
/// Please note that it uses a [`Vec`] to remember expected symbols. If you find this to be too slow, you can
/// implement [`Error`] for your own error type or use [`Simple`] instead.
// TODO: Impl `Clone`
pub struct Rich<'a, I: Input<'a>> {
    span: I::Span,
    reason: RichReason<'a, I>,
}

impl<'a, I: Input<'a>> Rich<'a, I> {
    fn inner_fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        token: fn(&I::Token, &mut fmt::Formatter<'_>) -> fmt::Result,
        span: fn(&I::Span, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        match &self.reason {
            RichReason::ExpectedFound { expected, found } => {
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

impl<'a, I: Input<'a>> Rich<'a, I> {
    /// Create an error with a custom message and span
    pub fn custom<M: ToString>(span: I::Span, msg: M) -> Self {
        Rich {
            span,
            reason: RichReason::Custom(msg.to_string()),
        }
    }

    /// Get the span associated with this error
    pub fn span(&self) -> I::Span
    where
        I::Span: Clone,
    {
        self.span.clone()
    }

    /// Get the reason fro this error
    pub fn reason(&self) -> &RichReason<'a, I> {
        &self.reason
    }

    /// Get an iterator over the expected items associated with this error
    pub fn expected(&self) -> alloc::vec::IntoIter<Option<&I::Token>> {
        fn push_expected<'a, 'b, I: Input<'b>>(
            reason: &'a RichReason<'b, I>,
            v: &mut Vec<Option<&'a I::Token>>,
        ) {
            match reason {
                RichReason::ExpectedFound { expected, .. } => {
                    v.extend(expected.iter().map(|e| e.as_ref()))
                }
                RichReason::Custom(_) => {}
                RichReason::Many(many) => many.iter().for_each(|r| push_expected(r, v)),
            }
        }
        let mut v = Vec::new();
        push_expected(&self.reason, &mut v);
        v.into_iter()
    }

    /// Get an iterator over the items found by this error
    pub fn found(&self) -> Option<&I::Token> {
        self.reason.found()
    }
}

impl<'a, I: Input<'a>> Error<'a, I> for Rich<'a, I>
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

impl<'a, I: Input<'a>> PartialEq for Rich<'a, I>
where
    I::Token: PartialEq,
    I::Span: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.span == other.span && self.reason == other.reason
    }
}

impl<'a, I: Input<'a>> fmt::Debug for Rich<'a, I>
where
    I::Span: fmt::Debug,
    I::Token: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner_fmt(f, I::Token::fmt, I::Span::fmt)
    }
}

impl<'a, I: Input<'a>> fmt::Display for Rich<'a, I>
where
    I::Span: fmt::Display,
    I::Token: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner_fmt(f, I::Token::fmt, I::Span::fmt)
    }
}

fn write_token<T>(
    f: &mut fmt::Formatter,
    writer: fn(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
    tok: &Option<T>,
) -> fmt::Result {
    match tok {
        Some(tok) => writer(tok, f),
        None => write!(f, "end of input"),
    }
}
