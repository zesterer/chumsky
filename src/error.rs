//! Error types, traits and utilities.
//!
//! *“I like the cover," he said. "Don't Panic. It's the first helpful or intelligible thing anybody's said to me all
//! day.”*
//!
//! You can implement the [`Error`] trait to create your own parser errors, or you can use one provided by the crate
//! like [`Cheap`], [`Simple`] or [`Rich`].

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

/// A very cheap error type that tracks only the error span. This type is most useful when you want fast parsing but do
/// not particularly care about the quality of error messages.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Cheap<S = SimpleSpan<usize>> {
    span: S,
}

impl<'a, I: Input<'a>> Error<'a, I> for Cheap<I::Span> {
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        _expected: E,
        _found: Option<I::Token>,
        span: I::Span,
    ) -> Self {
        Self { span }
    }
}

impl<S> fmt::Debug for Cheap<S>
where
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "at {:?}", self.span)?;
        Ok(())
    }
}

impl<S> fmt::Display for Cheap<S>
where
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// A simple error type that tracks the error span and found token. This type is most useful when you want fast parsing
/// but do not particularly care about the quality of error messages.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Simple<T, S = SimpleSpan<usize>> {
    span: S,
    found: Option<T>,
}

impl<T, S> Simple<T, S> {
    /// Transform this error's tokens using the given function.
    ///
    /// This is useful when you wish to combine errors from multiple compilation passes (lexing and parsing, say) where
    /// the token type for each pass is different (`char` vs `MyToken`, say).
    pub fn map_token<U, F: FnMut(T) -> U>(self, f: F) -> Simple<U, S> {
        Simple {
            span: self.span,
            found: self.found.map(f),
        }
    }
}

impl<'a, I: Input<'a>> Error<'a, I> for Simple<I::Token, I::Span> {
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        _expected: E,
        found: Option<I::Token>,
        span: I::Span,
    ) -> Self {
        Self { span, found }
    }
}

impl<T, S> fmt::Debug for Simple<T, S>
where
    T: fmt::Debug,
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "found ")?;
        write_token(f, T::fmt, &self.found)?;
        write!(f, " at {:?}", self.span)?;
        Ok(())
    }
}

impl<T, S> fmt::Display for Simple<T, S>
where
    T: fmt::Debug,
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

// TODO: Maybe should make ExpectedFound encapsulated a bit more
/// The reason for a [`Rich`] error
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum RichReason<T> {
    /// An unexpected input was found
    ExpectedFound {
        /// The tokens expected
        expected: Vec<Option<T>>,
        /// The tokens found
        found: Option<T>,
    },
    /// An error with a custom message
    Custom(String),
    /// Multiple unrelated reasons were merged
    Many(Vec<RichReason<T>>),
}

impl<T> RichReason<T> {
    /// Return the token that was found by this error reason. `None` implies that the end of input was expected.
    fn found(&self) -> Option<&T> {
        match self {
            RichReason::ExpectedFound { found, .. } => found.as_ref(),
            RichReason::Custom(_) => None,
            RichReason::Many(many) => many.iter().find_map(|r| r.found()),
        }
    }

    /// Transform this error's tokens using the given function.
    ///
    /// This is useful when you wish to combine errors from multiple compilation passes (lexing and parsing, say) where
    /// the token type for each pass is different (`char` vs `MyToken`, say).
    pub fn map_token<U, F: FnMut(T) -> U>(self, mut f: F) -> RichReason<U> {
        fn map_token_inner<T, U, F: FnMut(T) -> U>(
            reason: RichReason<T>,
            mut f: &mut F,
        ) -> RichReason<U> {
            match reason {
                RichReason::ExpectedFound { expected, found } => RichReason::ExpectedFound {
                    expected: expected.into_iter().map(|tok| tok.map(&mut f)).collect(),
                    found: found.map(f),
                },
                RichReason::Custom(msg) => RichReason::Custom(msg),
                RichReason::Many(reasons) => {
                    RichReason::Many(reasons.into_iter().map(|r| map_token_inner(r, f)).collect())
                }
            }
        }

        map_token_inner(self, &mut f)
    }
}

impl<T> RichReason<T>
where
    T: PartialEq,
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

/// A rich default error type that tracks error spans, expected inputs, and the actual input found at an error site.
///
/// Please note that it uses a [`Vec`] to remember expected symbols. If you find this to be too slow, you can
/// implement [`Error`] for your own error type or use [`Simple`] instead.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Rich<T, S = SimpleSpan<usize>> {
    span: S,
    reason: RichReason<T>,
}

impl<T, S> Rich<T, S> {
    fn inner_fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        token: fn(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
        span: fn(&S, &mut fmt::Formatter<'_>) -> fmt::Result,
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

impl<T, S> Rich<T, S> {
    /// Create an error with a custom message and span
    pub fn custom<M: ToString>(span: S, msg: M) -> Self {
        Rich {
            span,
            reason: RichReason::Custom(msg.to_string()),
        }
    }

    /// Get the span associated with this error
    pub fn span(&self) -> &S {
        &self.span
    }

    /// Get the reason fro this error
    pub fn reason(&self) -> &RichReason<T> {
        &self.reason
    }

    /// Get an iterator over the expected items associated with this error
    pub fn expected(&self) -> alloc::vec::IntoIter<Option<&T>> {
        fn push_expected<'a, T>(reason: &'a RichReason<T>, v: &mut Vec<Option<&'a T>>) {
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

    /// Get the token found by this error when parsing. `None` implies that the error expected the end of input.
    pub fn found(&self) -> Option<&T> {
        self.reason.found()
    }

    /// Transform this error's tokens using the given function.
    ///
    /// This is useful when you wish to combine errors from multiple compilation passes (lexing and parsing, say) where
    /// the token type for each pass is different (`char` vs `MyToken`, say).
    pub fn map_token<U, F: FnMut(T) -> U>(self, f: F) -> Rich<U, S> {
        Rich {
            span: self.span,
            reason: self.reason.map_token(f),
        }
    }
}

impl<'a, I: Input<'a>> Error<'a, I> for Rich<I::Token, I::Span>
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

impl<T, S> fmt::Debug for Rich<T, S>
where
    T: fmt::Debug,
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner_fmt(f, T::fmt, S::fmt)
    }
}

impl<T, S> fmt::Display for Rich<T, S>
where
    T: fmt::Display,
    S: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner_fmt(f, T::fmt, S::fmt)
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
