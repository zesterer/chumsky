//! Error types, traits and utilities.
//!
//! *“I like the cover," he said. "Don't Panic. It's the first helpful or intelligible thing anybody's said to me all
//! day.”*
//!
//! You can implement the [`Error`] trait to create your own parser errors, or you can use one provided by the crate
//! like [`Cheap`], [`Simple`] or [`Rich`].

use super::*;
use alloc::{borrow::Cow, string::ToString};

pub use label::LabelError;

/// A trait that describes parser error types.
///
/// If you have a custom error type in your compiler, or your needs are not sufficiently met by [`Simple`], you should
/// implement this trait. If your error type has 'extra' features that allow for more specific error messages, you can
/// use the [`Parser::map_err`] or [`Parser::try_map`] functions to take advantage of these inline within your parser.
///
/// # Examples
///
/// ```
/// use chumsky::{prelude::*, error::{Error, LabelError}, util::MaybeRef, DefaultExpected};
/// type Span = SimpleSpan<usize>;
///
/// // A custom error type
/// #[derive(Debug, PartialEq)]
/// enum MyError {
///     ExpectedFound {
///         span: Span,
///         expected: Vec<DefaultExpected<'static, char>>,
///         found: Option<char>,
///     },
///     NotADigit(Span, char),
/// }
///
/// impl<'a> Error<'a, &'a str> for MyError {
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
/// impl<'a> LabelError<'a, &'a str, DefaultExpected<'a, char>> for MyError {
///     fn expected_found<Iter: IntoIterator<Item = DefaultExpected<'a, char>>>(
///         expected: Iter,
///         found: Option<MaybeRef<'a, char>>,
///         span: Span,
///     ) -> Self {
///         Self::ExpectedFound {
///             span,
///             expected: expected
///                 .into_iter()
///                 .map(|e| e.into_owned())
///                 .collect(),
///             found: found.as_deref().copied(),
///         }
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
// TODO: Add support for more specialised kinds of error: unclosed delimiters, and more
pub trait Error<'a, I: Input<'a>>:
    Sized + LabelError<'a, I, DefaultExpected<'a, I::Token>>
{
    /// Merge two errors that point to the same input together, combining their information.
    #[inline(always)]
    fn merge(self, other: Self) -> Self {
        #![allow(unused_variables)]
        self
    }
}

/// A ZST error type that tracks only whether a parse error occurred at all. This type is for when
/// you want maximum parse speed, at the cost of all error reporting.
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
///
/// let parser = just::<_, _, extra::Err<EmptyErr>>("valid");
/// let error = parser.parse("invalid").into_errors()[0];
///
/// assert_eq!(error, EmptyErr::default());
/// ```
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Copy, Clone, Default)]
pub struct EmptyErr(());

impl<'a, I: Input<'a>> Error<'a, I> for EmptyErr {}

impl<'a, I: Input<'a>, L> LabelError<'a, I, L> for EmptyErr {
    #[inline(always)]
    fn expected_found<E: IntoIterator<Item = L>>(
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

/// A very cheap error type that tracks only the error span ([`SimpleSpan`] by default).
/// This type is most useful when you want fast parsing but do not particularly care about the quality of error messages.
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
///
/// let parser = just::<_, _, extra::Err<Cheap>>("+");
/// let error = parser.parse("-").into_errors()[0];
///
/// assert_eq!(error.span(), &SimpleSpan::new((), 0..1));
/// ```
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Cheap<S = SimpleSpan<usize>> {
    span: S,
}

impl<S> Cheap<S> {
    /// Create a new [`Cheap`] error.
    pub fn new(span: S) -> Self {
        Self { span }
    }

    /// Get the span than that error related to.
    ///
    /// If the span type is unspecified, it is [`SimpleSpan`].
    pub fn span(&self) -> &S {
        &self.span
    }
}

impl<'a, I: Input<'a>> Error<'a, I> for Cheap<I::Span> {}

impl<'a, I: Input<'a>, L> LabelError<'a, I, L> for Cheap<I::Span> {
    #[inline]
    fn expected_found<E: IntoIterator<Item = L>>(
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

/// A simple error type that tracks the error span ([`SimpleSpan`] by default) and found token. This type is most useful when you want fast parsing
/// but do not particularly care about the quality of error messages.
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
///
/// let parser = just::<_, _, extra::Err<Simple<char>>>("+");
/// let error = parser.parse("-").into_errors()[0];
///
/// assert_eq!(error.span(), &SimpleSpan::new((), 0..1));
/// assert_eq!(error.found(), Some(&'-'));
/// ```
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Simple<'a, T, S = SimpleSpan<usize>> {
    span: S,
    found: Option<MaybeRef<'a, T>>,
}

impl<T, S> Simple<'_, T, S> {
    /// Get the span than that error related to.
    ///
    /// If the span type is unspecified, it is [`SimpleSpan`].
    pub fn span(&self) -> &S {
        &self.span
    }

    /// Get the token found by this error when parsing. `None` implies that the error expected the end of input.
    pub fn found(&self) -> Option<&T> {
        self.found.as_deref()
    }
}

impl<'a, T, S> Simple<'a, T, S> {
    /// Create a new [`Simple`] error.
    pub fn new(found: Option<MaybeRef<'a, T>>, span: S) -> Self {
        Self { span, found }
    }

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

impl<'a, I: Input<'a>> Error<'a, I> for Simple<'a, I::Token, I::Span> {}

impl<'a, I: Input<'a>, L> LabelError<'a, I, L> for Simple<'a, I::Token, I::Span> {
    #[inline]
    fn expected_found<E: IntoIterator<Item = L>>(
        _expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        Self { span, found }
    }
}

impl<T, S> fmt::Debug for Simple<'_, T, S>
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

impl<T, S> fmt::Display for Simple<'_, T, S>
where
    T: fmt::Debug,
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// An expected pattern for a [`Rich`] error.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum RichPattern<'a, T> {
    /// A specific token.
    Token(MaybeRef<'a, T>),
    /// A labelled pattern.
    Label(Cow<'a, str>),
    /// A specific keyword.
    Identifier(String),
    /// Anything other than the end of input.
    Any,
    /// Something other than the provided input.
    SomethingElse,
    /// The end of input.
    EndOfInput,
}

impl<'a, T> From<DefaultExpected<'a, T>> for RichPattern<'a, T> {
    fn from(expected: DefaultExpected<'a, T>) -> Self {
        match expected {
            DefaultExpected::Token(tok) => Self::Token(tok),
            DefaultExpected::Any => Self::Any,
            DefaultExpected::SomethingElse => Self::SomethingElse,
            DefaultExpected::EndOfInput => Self::EndOfInput,
        }
    }
}

impl<'a, Slice: core::fmt::Debug, T> From<text::TextExpected<Slice>> for RichPattern<'a, T> {
    fn from(expected: text::TextExpected<Slice>) -> Self {
        match expected {
            text::TextExpected::Whitespace => Self::Label(Cow::Borrowed("whitespace")),
            text::TextExpected::InlineWhitespace => Self::Label(Cow::Borrowed("inline whitespace")),
            text::TextExpected::Newline => Self::Label(Cow::Borrowed("newline")),
            text::TextExpected::Digit(start, _end) if start > 0 => {
                Self::Label(Cow::Borrowed("non-zero digit"))
            }
            text::TextExpected::Digit(_, _) => Self::Label(Cow::Borrowed("digit")),
            text::TextExpected::AnyIdentifier => Self::Label(Cow::Borrowed("identifier")),
            text::TextExpected::Identifier(i) => Self::Identifier(alloc::format!("{i:?}")),
            text::TextExpected::Int => Self::Label(Cow::Borrowed("int")),
        }
    }
}

impl<'a, T> From<MaybeRef<'a, T>> for RichPattern<'a, T> {
    fn from(tok: MaybeRef<'a, T>) -> Self {
        Self::Token(tok)
    }
}

impl<T> From<&'static str> for RichPattern<'_, T> {
    fn from(label: &'static str) -> Self {
        Self::Label(Cow::Borrowed(label))
    }
}

impl<T> From<String> for RichPattern<'_, T> {
    fn from(label: String) -> Self {
        Self::Label(Cow::Owned(label))
    }
}

impl From<char> for RichPattern<'_, char> {
    fn from(c: char) -> Self {
        Self::Token(MaybeRef::Val(c))
    }
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
            Self::Label(l) => RichPattern::Label(l),
            Self::Identifier(i) => RichPattern::Identifier(i),
            Self::Any => RichPattern::Any,
            Self::SomethingElse => RichPattern::SomethingElse,
            Self::EndOfInput => RichPattern::EndOfInput,
        }
    }

    /// Convert this pattern into an owned version of itself by cloning any borrowed internal tokens, if necessary.
    pub fn into_owned<'b>(self) -> RichPattern<'b, T>
    where
        T: Clone,
    {
        match self {
            Self::Token(tok) => RichPattern::Token(tok.into_owned()),
            Self::Label(l) => RichPattern::Label(Cow::Owned(l.into_owned())),
            Self::Identifier(i) => RichPattern::Identifier(i),
            Self::Any => RichPattern::Any,
            Self::SomethingElse => RichPattern::SomethingElse,
            Self::EndOfInput => RichPattern::EndOfInput,
        }
    }

    fn write(
        &self,
        f: &mut fmt::Formatter,
        mut fmt_token: impl FnMut(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        match self {
            Self::Token(tok) => {
                write!(f, "'")?;
                fmt_token(tok, f)?;
                write!(f, "'")
            }
            Self::Label(l) => write!(f, "{l}"),
            Self::Identifier(i) => write!(f, "'{i}'"),
            Self::Any => write!(f, "any"),
            Self::SomethingElse => write!(f, "something else"),
            Self::EndOfInput => write!(f, "end of input"),
        }
    }
}

impl<T> fmt::Debug for RichPattern<'_, T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.write(f, |t, f| write!(f, "{t:?}"))
    }
}

impl<T> fmt::Display for RichPattern<'_, T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write(f, |t, f| write!(f, "{t}"))
    }
}

/// The reason for a [`Rich`] error.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
}

impl<'a, T> RichReason<'a, T> {
    /// Return the token that was found by this error reason. `None` implies that the end of input was expected.
    pub fn found(&self) -> Option<&T> {
        match self {
            Self::ExpectedFound { found, .. } => found.as_deref(),
            Self::Custom(_) => None,
        }
    }

    /// Convert this reason into an owned version of itself by cloning any borrowed internal tokens, if necessary.
    pub fn into_owned<'b>(self) -> RichReason<'b, T>
    where
        T: Clone,
    {
        match self {
            Self::ExpectedFound { found, expected } => RichReason::ExpectedFound {
                expected: expected.into_iter().map(RichPattern::into_owned).collect(),
                found: found.map(MaybeRef::into_owned),
            },
            Self::Custom(msg) => RichReason::Custom(msg),
        }
    }

    fn take_found(&mut self) -> Option<MaybeRef<'a, T>> {
        match self {
            RichReason::ExpectedFound { found, .. } => found.take(),
            RichReason::Custom(_) => None,
        }
    }

    /// Transform this `RichReason`'s tokens using the given function.
    ///
    /// This is useful when you wish to combine errors from multiple compilation passes (lexing and parsing, say) where
    /// the token type for each pass is different (`char` vs `MyToken`, say).
    pub fn map_token<U, F: FnMut(T) -> U>(self, mut f: F) -> RichReason<'a, U>
    where
        T: Clone,
    {
        match self {
            RichReason::ExpectedFound { expected, found } => RichReason::ExpectedFound {
                expected: expected
                    .into_iter()
                    .map(|pat| pat.map_token(&mut f))
                    .collect(),
                found: found.map(|found| f(found.into_inner()).into()),
            },
            RichReason::Custom(msg) => RichReason::Custom(msg),
        }
    }

    fn inner_fmt<S>(
        &self,
        f: &mut fmt::Formatter<'_>,
        mut fmt_token: impl FnMut(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
        mut fmt_span: impl FnMut(&S, &mut fmt::Formatter<'_>) -> fmt::Result,
        span: Option<&S>,
        context: &[(RichPattern<'a, T>, S)],
    ) -> fmt::Result {
        match self {
            RichReason::ExpectedFound { expected, found } => {
                write!(f, "found ")?;
                write_token(f, &mut fmt_token, found.as_deref())?;
                if let Some(span) = span {
                    write!(f, " at ")?;
                    fmt_span(span, f)?;
                }
                write!(f, " expected ")?;
                match &expected[..] {
                    [] => write!(f, "something else")?,
                    [expected] => expected.write(f, &mut fmt_token)?,
                    _ => {
                        for expected in &expected[..expected.len() - 1] {
                            expected.write(f, &mut fmt_token)?;
                            write!(f, ", ")?;
                        }
                        write!(f, "or ")?;
                        expected.last().unwrap().write(f, &mut fmt_token)?;
                    }
                }
            }
            RichReason::Custom(msg) => {
                write!(f, "{msg}")?;
                if let Some(span) = span {
                    write!(f, " at ")?;
                    fmt_span(span, f)?;
                }
            }
        }
        for (l, s) in context {
            write!(f, " in ")?;
            l.write(f, &mut fmt_token)?;
            write!(f, " at ")?;
            fmt_span(s, f)?;
        }
        Ok(())
    }
}

impl<T> RichReason<'_, T>
where
    T: PartialEq,
{
    #[inline]
    fn flat_merge(self, other: Self) -> Self {
        match (self, other) {
            // Prefer first error, if ambiguous
            (a @ RichReason::Custom(_), _) => a,
            (_, b @ RichReason::Custom(_)) => b,
            (
                RichReason::ExpectedFound {
                    expected: mut this_expected,
                    found,
                },
                RichReason::ExpectedFound {
                    expected: mut other_expected,
                    ..
                },
            ) => {
                // Try to avoid allocations if we possibly can by using the longer vector
                if other_expected.len() > this_expected.len() {
                    core::mem::swap(&mut this_expected, &mut other_expected);
                }
                for expected in other_expected {
                    if !this_expected[..].contains(&expected) {
                        this_expected.push(expected);
                    }
                }
                RichReason::ExpectedFound {
                    expected: this_expected,
                    found,
                }
            }
        }
    }
}

impl<T> fmt::Display for RichReason<'_, T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner_fmt(f, T::fmt, |_: &(), _| Ok(()), None, &[])
    }
}

/// A rich default error type that tracks error spans, expected inputs, and the actual input found at an error site.
///
/// Please note that it uses a [`Vec`] to remember expected symbols. If you find this to be too slow, you can
/// implement [`Error`] for your own error type or use [`Simple`] instead.
///
/// This error type stores a span ([`SimpleSpan`] by default), a [`RichReason`], and a list of expected [`RichPattern`] with their spans.
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
/// use chumsky::error::{RichReason, RichPattern};
///
/// let parser = one_of::<_, _, extra::Err<Rich<char>>>("1234");
/// let error = parser.parse("5").into_errors()[0].clone();
///
/// assert_eq!(error.span(), &SimpleSpan::new((), 0..1));
/// assert!(matches!(error.reason(), &RichReason::ExpectedFound {..}));
/// assert_eq!(error.found(), Some(&'5'));
///
/// ```
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rich<'a, T, S = SimpleSpan<usize>> {
    span: S,
    reason: Box<RichReason<'a, T>>,
    context: Vec<(RichPattern<'a, T>, S)>,
}

impl<T, S> Rich<'_, T, S> {
    fn inner_fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        fmt_token: impl FnMut(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
        fmt_span: impl FnMut(&S, &mut fmt::Formatter<'_>) -> fmt::Result,
        with_spans: bool,
    ) -> fmt::Result {
        self.reason.inner_fmt(
            f,
            fmt_token,
            fmt_span,
            if with_spans { Some(&self.span) } else { None },
            &self.context,
        )
    }
}

impl<'a, T, S> Rich<'a, T, S> {
    /// Create an error with a custom message and span
    #[inline]
    pub fn custom<M: ToString>(span: S, msg: M) -> Self {
        Rich {
            span,
            reason: Box::new(RichReason::Custom(msg.to_string())),
            context: Vec::new(),
        }
    }

    /// Get the span associated with this error.
    ///
    /// If the span type is unspecified, it is [`SimpleSpan`].
    pub fn span(&self) -> &S {
        &self.span
    }

    /// Get the reason for this error.
    pub fn reason(&self) -> &RichReason<'a, T> {
        &self.reason
    }

    /// Take the reason from this error.
    pub fn into_reason(self) -> RichReason<'a, T> {
        *self.reason
    }

    /// Get the token found by this error when parsing. `None` implies that the error expected the end of input.
    pub fn found(&self) -> Option<&T> {
        self.reason.found()
    }

    /// Return an iterator over the labelled contexts of this error, from least general to most.
    ///
    /// 'Context' here means parser patterns that the parser was in the process of parsing when the error occurred. To
    /// add labelled contexts, see [`Parser::labelled`].
    pub fn contexts(&self) -> impl Iterator<Item = (&RichPattern<'a, T>, &S)> {
        self.context.iter().map(|(l, s)| (l, s))
    }

    /// Convert this error into an owned version of itself by cloning any borrowed internal tokens, if necessary.
    pub fn into_owned<'b>(self) -> Rich<'b, T, S>
    where
        T: Clone,
    {
        Rich {
            reason: Box::new(self.reason.into_owned()),
            context: self
                .context
                .into_iter()
                .map(|(p, s)| (p.into_owned(), s))
                .collect(),
            ..self
        }
    }

    /// Get an iterator over the expected items associated with this error
    pub fn expected(&self) -> impl ExactSizeIterator<Item = &RichPattern<'a, T>> {
        match &*self.reason {
            RichReason::ExpectedFound { expected, .. } => expected.iter(),
            RichReason::Custom(_) => [].iter(),
        }
    }

    /// Transform this error's tokens using the given function.
    ///
    /// This is useful when you wish to combine errors from multiple compilation passes (lexing and parsing, say) where
    /// the token type for each pass is different (`char` vs `MyToken`, say).
    pub fn map_token<U, F: FnMut(T) -> U>(self, mut f: F) -> Rich<'a, U, S>
    where
        T: Clone,
    {
        Rich {
            span: self.span,
            reason: Box::new(self.reason.map_token(&mut f)),
            context: self
                .context
                .into_iter()
                .map(|(p, s)| (p.map_token(&mut f), s))
                .collect(),
        }
    }
}

impl<'a, I: Input<'a>> Error<'a, I> for Rich<'a, I::Token, I::Span>
where
    I::Token: PartialEq,
{
    #[inline]
    fn merge(self, other: Self) -> Self {
        let new_reason = self.reason.flat_merge(*other.reason);
        Self {
            span: self.span,
            reason: Box::new(new_reason),
            context: self.context, // TOOD: Merge contexts
        }
    }
}

impl<'a, I: Input<'a>, L> LabelError<'a, I, L> for Rich<'a, I::Token, I::Span>
where
    I::Token: PartialEq,
    L: Into<RichPattern<'a, I::Token>>,
{
    #[inline]
    fn expected_found<E: IntoIterator<Item = L>>(
        expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        Self {
            span,
            reason: Box::new(RichReason::ExpectedFound {
                expected: expected.into_iter().map(|tok| tok.into()).collect(),
                found,
            }),
            context: Vec::new(),
        }
    }

    #[inline]
    fn merge_expected_found<E: IntoIterator<Item = L>>(
        mut self,
        new_expected: E,
        new_found: Option<MaybeRef<'a, I::Token>>,
        _span: I::Span,
    ) -> Self {
        match &mut *self.reason {
            RichReason::ExpectedFound { expected, found } => {
                for new_expected in new_expected {
                    let new_expected = new_expected.into();
                    if !expected[..].contains(&new_expected) {
                        expected.push(new_expected);
                    }
                }
                *found = found.take().or(new_found); //land
            }
            RichReason::Custom(_) => {}
        }
        // TOOD: Merge contexts
        self
    }

    #[inline]
    fn replace_expected_found<E: IntoIterator<Item = L>>(
        mut self,
        new_expected: E,
        new_found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        self.span = span;
        match &mut *self.reason {
            RichReason::ExpectedFound { expected, found } => {
                expected.clear();
                expected.extend(new_expected.into_iter().map(|tok| tok.into()));
                *found = new_found;
            }
            _ => {
                *self.reason = RichReason::ExpectedFound {
                    expected: new_expected.into_iter().map(|tok| tok.into()).collect(),
                    found: new_found,
                };
            }
        }
        self.context.clear();
        self
    }

    #[inline]
    fn label_with(&mut self, label: L) {
        // Opportunistically attempt to reuse allocations if we can
        match &mut *self.reason {
            RichReason::ExpectedFound { expected, found: _ } => {
                expected.clear();
                expected.push(label.into());
            }
            _ => {
                *self.reason = RichReason::ExpectedFound {
                    expected: vec![label.into()],
                    found: self.reason.take_found(),
                };
            }
        }
    }

    #[inline]
    fn in_context(&mut self, label: L, span: I::Span) {
        let label = label.into();
        if self.context.iter().all(|(l, _)| l != &label) {
            self.context.push((label, span));
        }
    }
}

impl<T, S> fmt::Debug for Rich<'_, T, S>
where
    T: fmt::Debug,
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner_fmt(f, T::fmt, S::fmt, true)
    }
}

impl<T, S> fmt::Display for Rich<'_, T, S>
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
    mut fmt_token: impl FnMut(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
    tok: Option<&T>,
) -> fmt::Result {
    match tok {
        Some(tok) => {
            write!(f, "'")?;
            fmt_token(tok, f)?;
            write!(f, "'")
        }
        None => write!(f, "end of input"),
    }
}
