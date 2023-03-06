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
///     ExpectedFound {
///         span: Span,
///         expected: Vec<Option<char>>,
///         found: Option<char>,
///     },
///     NotADigit(Span, char),
/// }
///
/// impl<'a> chumsky::error::Error<'a, &'a str> for MyError {
///     fn expected_found<Iter: IntoIterator<Item = Option<chumsky::MaybeRef<'a, char>>>>(
///         expected: Iter,
///         found: Option<chumsky::MaybeRef<'a, char>>,
///         span: Span,
///     ) -> Self {
///         Self::ExpectedFound {
///             span,
///             expected: expected.into_iter().map(|e| e.as_deref().copied()).collect(),
///             found: found.as_deref().copied(),
///         }
///     }
///
///     fn merge(mut self, mut other: Self) -> Self {
///         if let (Self::ExpectedFound { expected, .. }, Self::ExpectedFound { expected: expected_other, .. }) = (
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
    fn expected_found<E: IntoIterator<Item = Option<MaybeRef<'a, I::Token>>>>(
        expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
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
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Copy, Clone, Default)]
pub struct EmptyErr(());

impl<'a, I: Input<'a>> Error<'a, I> for EmptyErr {
    fn expected_found<E: IntoIterator<Item = Option<MaybeRef<'a, I::Token>>>>(
        _: E,
        _: Option<MaybeRef<'a, I::Token>>,
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
    fn expected_found<E: IntoIterator<Item = Option<MaybeRef<'a, I::Token>>>>(
        _expected: E,
        _found: Option<MaybeRef<'a, I::Token>>,
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
pub struct Simple<'a, T, S = SimpleSpan<usize>> {
    span: S,
    found: Option<MaybeRef<'a, T>>,
}

impl<'a, T, S> Simple<'a, T, S> {
    /// Transform this error's tokens using the given function.
    ///
    /// This is useful when you wish to combine errors from multiple compilation passes (lexing and parsing, say) where
    /// the token type for each pass is different (`char` vs `MyToken`, say).
    pub fn map_token<U, F: FnOnce(T) -> U>(self, f: F) -> Simple<'a, U, S>
    where
        T: Clone,
    {
        Simple {
            span: self.span,
            found: self.found.map(|found| f(found.into_inner()).into()),
        }
    }
}

impl<'a, I: Input<'a>> Error<'a, I> for Simple<'a, I::Token, I::Span> {
    fn expected_found<E: IntoIterator<Item = Option<MaybeRef<'a, I::Token>>>>(
        _expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        Self { span, found }
    }
}

impl<'a, T, S> fmt::Debug for Simple<'a, T, S>
where
    T: fmt::Debug,
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "found ")?;
        write_token(f, T::fmt, self.found.as_deref())?;
        write!(f, " at {:?}", self.span)?;
        Ok(())
    }
}

impl<'a, T, S> fmt::Display for Simple<'a, T, S>
where
    T: fmt::Debug,
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// An expected pattern for a [`Rich`] error.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum RichPattern<'a, T> {
    /// A specific token was expected.
    Token(MaybeRef<'a, T>),
    /// A labelled pattern was expected.
    Label(&'static str),
    /// The end of input was expected.
    EndOfInput,
}

impl<'a, T> RichPattern<'a, T> {
    /// Transform this pattern's tokens using the given function.
    ///
    /// This is useful when you wish to combine errors from multiple compilation passes (lexing and parsing, say) where
    /// the token type for each pass is different (`char` vs `MyToken`, say).
    pub fn map_token<U, F: FnMut(T) -> U>(self, mut f: F) -> RichPattern<'a, U>
    where
        T: Clone,
    {
        match self {
            Self::Token(t) => RichPattern::Token(f(t.into_inner()).into()),
            Self::Label(s) => RichPattern::Label(s),
            Self::EndOfInput => RichPattern::EndOfInput,
        }
    }

    fn write(
        &self,
        f: &mut fmt::Formatter,
        writer: fn(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        match self {
            Self::Token(t) => {
                write!(f, "'")?;
                writer(t, f)?;
                write!(f, "'")
            }
            Self::Label(s) => write!(f, "{}", s),
            Self::EndOfInput => write!(f, "end of input"),
        }
    }
}

impl<'a, T> fmt::Debug for RichPattern<'a, T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Token(t) => write!(f, "{:?}", t),
            Self::Label(s) => write!(f, "{}", s),
            Self::EndOfInput => write!(f, "end of input"),
        }
    }
}

impl<'a, T> fmt::Display for RichPattern<'a, T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Token(t) => write!(f, "'{}'", &**t),
            Self::Label(s) => write!(f, "{}", s),
            Self::EndOfInput => write!(f, "end of input"),
        }
    }
}

// TODO: Maybe should make ExpectedFound encapsulated a bit more
/// The reason for a [`Rich`] error.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum RichReason<'a, T> {
    /// An unexpected input was found
    ExpectedFound {
        /// The tokens expected
        expected: Vec<RichPattern<'a, T>>,
        /// The tokens found
        found: Option<MaybeRef<'a, T>>,
    },
    /// An error with a custom message
    Custom(String),
    /// Multiple unrelated reasons were merged
    Many(Vec<Self>),
}

impl<'a, T> RichReason<'a, T> {
    /// Return the token that was found by this error reason. `None` implies that the end of input was expected.
    pub fn found(&self) -> Option<&T> {
        match self {
            RichReason::ExpectedFound { found, .. } => found.as_deref(),
            RichReason::Custom(_) => None,
            RichReason::Many(many) => many.iter().find_map(|r| r.found()),
        }
    }

    fn take_found(&mut self) -> Option<MaybeRef<'a, T>> {
        match self {
            RichReason::ExpectedFound { found, .. } => found.take(),
            RichReason::Custom(_) => None,
            RichReason::Many(many) => many.into_iter().find_map(|r| r.take_found()),
        }
    }

    /// Transform this error's tokens using the given function.
    ///
    /// This is useful when you wish to combine errors from multiple compilation passes (lexing and parsing, say) where
    /// the token type for each pass is different (`char` vs `MyToken`, say).
    pub fn map_token<U, F: FnMut(T) -> U>(self, mut f: F) -> RichReason<'a, U>
    where
        T: Clone,
    {
        fn map_token_inner<'a, T: Clone, U, F: FnMut(T) -> U>(
            reason: RichReason<'a, T>,
            mut f: &mut F,
        ) -> RichReason<'a, U> {
            match reason {
                RichReason::ExpectedFound { expected, found } => RichReason::ExpectedFound {
                    expected: expected
                        .into_iter()
                        .map(|pat| pat.map_token(&mut f))
                        .collect(),
                    found: found.map(|found| f(found.into_inner()).into()),
                },
                RichReason::Custom(msg) => RichReason::Custom(msg),
                RichReason::Many(reasons) => {
                    RichReason::Many(reasons.into_iter().map(|r| map_token_inner(r, f)).collect())
                }
            }
        }

        map_token_inner(self, &mut f)
    }

    fn inner_fmt<S>(
        &self,
        f: &mut fmt::Formatter<'_>,
        token: fn(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
        write_span: fn(&S, &mut fmt::Formatter<'_>) -> fmt::Result,
        span: Option<&S>,
    ) -> fmt::Result {
        match self {
            RichReason::ExpectedFound { expected, found } => {
                write!(f, "found ")?;
                write_token(f, token, found.as_deref())?;
                if let Some(span) = span {
                    write!(f, " at ")?;
                    write_span(span, f)?;
                }
                write!(f, " expected ")?;
                match &expected[..] {
                    [] => write!(f, "something else")?,
                    [expected] => expected.write(f, token)?,
                    _ => {
                        for expected in &expected[..expected.len() - 1] {
                            expected.write(f, token)?;
                            write!(f, ", ")?;
                        }
                        write!(f, "or ")?;
                        expected.last().unwrap().write(f, token)?;
                    }
                }
            }
            RichReason::Custom(msg) => {
                write!(f, "{}", msg)?;
                if let Some(span) = span {
                    write!(f, " at ")?;
                    write_span(&span, f)?;
                }
            }
            RichReason::Many(_) => {
                write!(f, "multiple errors")?;
                if let Some(span) = span {
                    write!(f, " found at ")?;
                    write_span(span, f)?;
                }
            }
        }
        Ok(())
    }
}

impl<'a, T> RichReason<'a, T>
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
                    if !<[_]>::contains(&this_expected, &expected) {
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

impl<'a, T> fmt::Debug for RichReason<'a, T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner_fmt(f, T::fmt, |_: &(), _| Ok(()), None)
    }
}

impl<'a, T> fmt::Display for RichReason<'a, T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner_fmt(f, T::fmt, |_: &(), _| Ok(()), None)
    }
}

/// A rich default error type that tracks error spans, expected inputs, and the actual input found at an error site.
///
/// Please note that it uses a [`Vec`] to remember expected symbols. If you find this to be too slow, you can
/// implement [`Error`] for your own error type or use [`Simple`] instead.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Rich<'a, T, S = SimpleSpan<usize>> {
    span: S,
    reason: RichReason<'a, T>,
}

impl<'a, T, S> Rich<'a, T, S> {
    fn inner_fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        token: fn(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
        span: fn(&S, &mut fmt::Formatter<'_>) -> fmt::Result,
        with_spans: bool,
    ) -> fmt::Result {
        self.reason.inner_fmt(
            f,
            token,
            span,
            if with_spans { Some(&self.span) } else { None },
        )
    }
}

impl<'a, T, S> Rich<'a, T, S> {
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
    pub fn expected(&self) -> impl ExactSizeIterator<Item = &RichPattern<'a, T>> {
        fn push_expected<'a, 'b, T>(
            reason: &'b RichReason<'a, T>,
            v: &mut Vec<&'b RichPattern<'a, T>>,
        ) {
            match reason {
                RichReason::ExpectedFound { expected, .. } => v.extend(expected.iter()),
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
    pub fn map_token<U, F: FnMut(T) -> U>(self, f: F) -> Rich<'a, U, S>
    where
        T: Clone,
    {
        Rich {
            span: self.span,
            reason: self.reason.map_token(f),
        }
    }
}

impl<'a, I: Input<'a>> Error<'a, I> for Rich<'a, I::Token, I::Span>
where
    I::Token: PartialEq,
{
    fn expected_found<E: IntoIterator<Item = Option<MaybeRef<'a, I::Token>>>>(
        expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        Self {
            span,
            reason: RichReason::ExpectedFound {
                expected: expected
                    .into_iter()
                    .map(|tok| {
                        if let Some(tok) = tok {
                            RichPattern::Token(tok)
                        } else {
                            RichPattern::EndOfInput
                        }
                    })
                    .collect(),
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

#[cfg(feature = "label")]
impl<'a, I: Input<'a>> LabelError<'a, I, &'static str> for Rich<'a, I::Token, I::Span>
where
    I::Token: PartialEq,
{
    fn label_with(&mut self, label: &'static str) {
        self.reason = RichReason::ExpectedFound {
            expected: vec![RichPattern::Label(label)],
            found: self.reason.take_found(),
        }
    }
}

impl<'a, T, S> fmt::Debug for Rich<'a, T, S>
where
    T: fmt::Debug,
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner_fmt(f, T::fmt, S::fmt, true)
    }
}

impl<'a, T, S> fmt::Display for Rich<'a, T, S>
where
    T: fmt::Display,
    S: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner_fmt(f, T::fmt, S::fmt, false)
    }
}

fn write_token<T>(
    f: &mut fmt::Formatter,
    writer: fn(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
    tok: Option<&T>,
) -> fmt::Result {
    match tok {
        Some(tok) => {
            write!(f, "'")?;
            writer(tok, f)?;
            write!(f, "'")
        }
        None => write!(f, "end of input"),
    }
}
