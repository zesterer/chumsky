//! Error types, traits and utilities.
//!
//! *“I like the cover," he said. "Don't Panic. It's the first helpful or intelligible thing anybody's said to me all
//! day.”*
//!
//! You can implement the [`Error`] trait to create your own parser errors, or you can use one provided by the crate
//! like [`Cheap`], [`Simple`] or [`Rich`].

use super::*;
#[cfg(not(feature = "std"))]
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
/// use chumsky::{prelude::*, error::Error, util::MaybeRef};
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
/// impl<'a> Error<'a, &'a str> for MyError {
///     fn expected_found<Iter: IntoIterator<Item = Option<MaybeRef<'a, char>>>>(
///         expected: Iter,
///         found: Option<MaybeRef<'a, char>>,
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
// TODO: Add support for more specialised kinds of error: unclosed delimiters, and more
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
    #[inline(always)]
    fn merge(self, other: Self) -> Self {
        #![allow(unused_variables)]
        self
    }

    /// Fast path for `a.merge(Error::expected_found(...))` that may incur less overhead by, for example, reusing allocations.
    #[inline(always)]
    fn merge_expected_found<E: IntoIterator<Item = Option<MaybeRef<'a, I::Token>>>>(
        self,
        expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        self.merge(Self::expected_found(expected, found, span))
    }

    /// Fast path for `a = Error::expected_found(...)` that may incur less overhead by, for example, reusing allocations.
    #[inline(always)]
    fn replace_expected_found<E: IntoIterator<Item = Option<MaybeRef<'a, I::Token>>>>(
        self,
        expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        Self::expected_found(expected, found, span)
    }
}

/// A ZST error type that tracks only whether a parse error occurred at all. This type is for when
/// you want maximum parse speed, at the cost of all error reporting.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Copy, Clone, Default)]
pub struct EmptyErr(());

impl<'a, I: Input<'a>> Error<'a, I> for EmptyErr {
    #[inline(always)]
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
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Cheap<S = SimpleSpan<usize>> {
    span: S,
}

impl<S> Cheap<S> {
    /// Get the span than that error related to.
    pub fn span(&self) -> &S {
        &self.span
    }
}

impl<'a, I: Input<'a>> Error<'a, I> for Cheap<I::Span> {
    #[inline]
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
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Simple<'a, T, S = SimpleSpan<usize>> {
    span: S,
    found: Option<MaybeRef<'a, T>>,
}

impl<T, S> Simple<'_, T, S> {
    /// Get the span than that error related to.
    pub fn span(&self) -> &S {
        &self.span
    }

    /// Get the token, if any, that was found at the error location.
    pub fn found(&self) -> Option<&T> {
        self.found.as_deref()
    }
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
    #[inline]
    fn expected_found<E: IntoIterator<Item = Option<MaybeRef<'a, I::Token>>>>(
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
pub enum RichPattern<'a, T, L = &'static str> {
    /// A specific token was expected.
    Token(MaybeRef<'a, T>),
    /// A labelled pattern was expected.
    Label(L),
    /// The end of input was expected.
    EndOfInput,
}

impl<'a, T, L> RichPattern<'a, T, L> {
    /// Transform this pattern's tokens using the given function.
    ///
    /// This is useful when you wish to combine errors from multiple compilation passes (lexing and parsing, say) where
    /// the token type for each pass is different (`char` vs `MyToken`, say).
    pub fn map_token<U, F: FnMut(T) -> U>(self, mut f: F) -> RichPattern<'a, U, L>
    where
        T: Clone,
    {
        match self {
            Self::Token(t) => RichPattern::Token(f(t.into_inner()).into()),
            Self::Label(s) => RichPattern::Label(s),
            Self::EndOfInput => RichPattern::EndOfInput,
        }
    }

    /// Convert this pattern into an owned version of itself by cloning any borrowed internal tokens, if necessary.
    pub fn into_owned<'b>(self) -> RichPattern<'b, T, L>
    where
        T: Clone,
    {
        match self {
            Self::Token(tok) => RichPattern::Token(tok.into_owned()),
            Self::Label(label) => RichPattern::Label(label),
            Self::EndOfInput => RichPattern::EndOfInput,
        }
    }

    fn write(
        &self,
        f: &mut fmt::Formatter,
        mut fmt_token: impl FnMut(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
        mut fmt_label: impl FnMut(&L, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        match self {
            Self::Token(tok) => {
                write!(f, "'")?;
                fmt_token(tok, f)?;
                write!(f, "'")
            }
            Self::Label(label) => fmt_label(label, f),
            Self::EndOfInput => write!(f, "end of input"),
        }
    }
}

impl<T, L> fmt::Debug for RichPattern<'_, T, L>
where
    T: fmt::Debug,
    L: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Token(t) => write!(f, "{t:?}"),
            Self::Label(label) => write!(f, "{label:?}"),
            Self::EndOfInput => write!(f, "end of input"),
        }
    }
}

impl<T, L> fmt::Display for RichPattern<'_, T, L>
where
    T: fmt::Display,
    L: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Token(t) => write!(f, "'{}'", &**t),
            Self::Label(s) => write!(f, "{s}"),
            Self::EndOfInput => write!(f, "end of input"),
        }
    }
}

// TODO: Maybe should make ExpectedFound encapsulated a bit more
/// The reason for a [`Rich`] error.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RichReason<'a, T, L = &'static str> {
    /// An unexpected input was found
    ExpectedFound {
        /// The tokens expected
        expected: Vec<RichPattern<'a, T, L>>,
        /// The tokens found
        found: Option<MaybeRef<'a, T>>,
    },
    /// An error with a custom message
    Custom(String),
}

impl<'a, T, L> RichReason<'a, T, L> {
    /// Return the token that was found by this error reason. `None` implies that the end of input was expected.
    pub fn found(&self) -> Option<&T> {
        match self {
            Self::ExpectedFound { found, .. } => found.as_deref(),
            Self::Custom(_) => None,
        }
    }

    /// Convert this reason into an owned version of itself by cloning any borrowed internal tokens, if necessary.
    pub fn into_owned<'b>(self) -> RichReason<'b, T, L>
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

    #[cfg(feature = "label")]
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
    pub fn map_token<U, F: FnMut(T) -> U>(self, mut f: F) -> RichReason<'a, U, L>
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
        mut fmt_label: impl FnMut(&L, &mut fmt::Formatter<'_>) -> fmt::Result,
        span: Option<&S>,
        #[cfg(feature = "label")] context: &[(L, S)],
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
                    [expected] => expected.write(f, &mut fmt_token, &mut fmt_label)?,
                    _ => {
                        for expected in &expected[..expected.len() - 1] {
                            expected.write(f, &mut fmt_token, &mut fmt_label)?;
                            write!(f, ", ")?;
                        }
                        write!(f, "or ")?;
                        expected
                            .last()
                            .unwrap()
                            .write(f, &mut fmt_token, &mut fmt_label)?;
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
        #[cfg(feature = "label")]
        for (l, s) in context {
            write!(f, " in ")?;
            fmt_label(l, f)?;
            write!(f, " at ")?;
            fmt_span(s, f)?;
        }
        Ok(())
    }
}

impl<T, L> RichReason<'_, T, L>
where
    T: PartialEq,
    L: PartialEq,
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

impl<T, L> fmt::Display for RichReason<'_, T, L>
where
    T: fmt::Display,
    L: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner_fmt(
            f,
            T::fmt,
            |_: &(), _| Ok(()),
            L::fmt,
            None,
            #[cfg(feature = "label")]
            &[],
        )
    }
}

/// A rich default error type that tracks error spans, expected inputs, and the actual input found at an error site.
///
/// Please note that it uses a [`Vec`] to remember expected symbols. If you find this to be too slow, you can
/// implement [`Error`] for your own error type or use [`Simple`] instead.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Rich<'a, T, S = SimpleSpan<usize>, L = &'static str> {
    span: S,
    reason: Box<RichReason<'a, T, L>>,
    #[cfg(feature = "label")]
    context: Vec<(L, S)>,
}

impl<T, S, L> Rich<'_, T, S, L> {
    fn inner_fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        fmt_token: impl FnMut(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
        fmt_span: impl FnMut(&S, &mut fmt::Formatter<'_>) -> fmt::Result,
        fmt_label: impl FnMut(&L, &mut fmt::Formatter<'_>) -> fmt::Result,
        with_spans: bool,
    ) -> fmt::Result {
        self.reason.inner_fmt(
            f,
            fmt_token,
            fmt_span,
            fmt_label,
            if with_spans { Some(&self.span) } else { None },
            #[cfg(feature = "label")]
            &self.context,
        )
    }
}

impl<'a, T, S, L> Rich<'a, T, S, L> {
    /// Create an error with a custom message and span
    #[inline]
    pub fn custom<M: ToString>(span: S, msg: M) -> Self {
        Rich {
            span,
            reason: Box::new(RichReason::Custom(msg.to_string())),
            #[cfg(feature = "label")]
            context: Vec::new(),
        }
    }

    /// Get the span associated with this error.
    pub fn span(&self) -> &S {
        &self.span
    }

    /// Get the reason for this error.
    pub fn reason(&self) -> &RichReason<'a, T, L> {
        &self.reason
    }

    /// Take the reason from this error.
    pub fn into_reason(self) -> RichReason<'a, T, L> {
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
    #[cfg(feature = "label")]
    pub fn contexts(&self) -> impl Iterator<Item = (&L, &S)> {
        self.context.iter().map(|(l, s)| (l, s))
    }

    /// Convert this error into an owned version of itself by cloning any borrowed internal tokens, if necessary.
    pub fn into_owned<'b>(self) -> Rich<'b, T, S, L>
    where
        T: Clone,
    {
        Rich {
            reason: Box::new(self.reason.into_owned()),
            ..self
        }
    }

    /// Get an iterator over the expected items associated with this error
    pub fn expected(&self) -> impl ExactSizeIterator<Item = &RichPattern<'a, T, L>> {
        match &*self.reason {
            RichReason::ExpectedFound { expected, .. } => expected.iter(),
            RichReason::Custom(_) => [].iter(),
        }
    }

    /// Transform this error's tokens using the given function.
    ///
    /// This is useful when you wish to combine errors from multiple compilation passes (lexing and parsing, say) where
    /// the token type for each pass is different (`char` vs `MyToken`, say).
    pub fn map_token<U, F: FnMut(T) -> U>(self, f: F) -> Rich<'a, U, S, L>
    where
        T: Clone,
    {
        Rich {
            span: self.span,
            reason: Box::new(self.reason.map_token(f)),
            #[cfg(feature = "label")]
            context: self.context,
        }
    }
}

impl<'a, I: Input<'a>, L> Error<'a, I> for Rich<'a, I::Token, I::Span, L>
where
    I::Token: PartialEq,
    L: PartialEq,
{
    #[inline]
    fn expected_found<E: IntoIterator<Item = Option<MaybeRef<'a, I::Token>>>>(
        expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        Self {
            span,
            reason: Box::new(RichReason::ExpectedFound {
                expected: expected
                    .into_iter()
                    .map(|tok| {
                        tok.map(RichPattern::Token)
                            .unwrap_or(RichPattern::EndOfInput)
                    })
                    .collect(),
                found,
            }),
            #[cfg(feature = "label")]
            context: Vec::new(),
        }
    }

    #[inline]
    fn merge(self, other: Self) -> Self {
        let new_reason = self.reason.flat_merge(*other.reason);
        Self {
            span: self.span,
            reason: Box::new(new_reason),
            #[cfg(feature = "label")]
            context: self.context, // TOOD: Merge contexts
        }
    }

    #[inline]
    fn merge_expected_found<E: IntoIterator<Item = Option<MaybeRef<'a, I::Token>>>>(
        mut self,
        new_expected: E,
        new_found: Option<MaybeRef<'a, I::Token>>,
        _span: I::Span,
    ) -> Self {
        match &mut *self.reason {
            RichReason::ExpectedFound { expected, found } => {
                for new_expected in new_expected {
                    let new_expected = new_expected
                        .map(RichPattern::Token)
                        .unwrap_or(RichPattern::EndOfInput);
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
    fn replace_expected_found<E: IntoIterator<Item = Option<MaybeRef<'a, I::Token>>>>(
        mut self,
        new_expected: E,
        new_found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        self.span = span;
        match &mut *self.reason {
            RichReason::ExpectedFound { expected, found } => {
                expected.clear();
                expected.extend(new_expected.into_iter().map(|tok| {
                    tok.map(RichPattern::Token)
                        .unwrap_or(RichPattern::EndOfInput)
                }));
                *found = new_found;
            }
            _ => {
                self.reason = Box::new(RichReason::ExpectedFound {
                    expected: new_expected
                        .into_iter()
                        .map(|tok| {
                            tok.map(RichPattern::Token)
                                .unwrap_or(RichPattern::EndOfInput)
                        })
                        .collect(),
                    found: new_found,
                });
            }
        }
        #[cfg(feature = "label")]
        self.context.clear();
        self
    }
}

#[cfg(feature = "label")]
impl<'a, I: Input<'a>, L> LabelError<'a, I, L> for Rich<'a, I::Token, I::Span, L>
where
    I::Token: PartialEq,
    L: PartialEq,
{
    #[inline]
    fn label_with(&mut self, label: L) {
        // Opportunistically attempt to reuse allocations if we can
        match &mut *self.reason {
            RichReason::ExpectedFound { expected, found: _ } => {
                expected.clear();
                expected.push(RichPattern::Label(label));
            }
            _ => {
                self.reason = Box::new(RichReason::ExpectedFound {
                    expected: vec![RichPattern::Label(label)],
                    found: self.reason.take_found(),
                });
            }
        }
    }

    #[inline]
    fn in_context(&mut self, label: L, span: I::Span) {
        if self.context.iter().all(|(l, _)| l != &label) {
            self.context.push((label, span));
        }
    }
}

impl<T, S, L> fmt::Debug for Rich<'_, T, S, L>
where
    T: fmt::Debug,
    S: fmt::Debug,
    L: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner_fmt(f, T::fmt, S::fmt, L::fmt, true)
    }
}

impl<T, S, L> fmt::Display for Rich<'_, T, S, L>
where
    T: fmt::Display,
    S: fmt::Display,
    L: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner_fmt(f, T::fmt, S::fmt, L::fmt, false)
    }
}

fn write_token<T>(
    f: &mut fmt::Formatter,
    mut fmt_token: impl FnMut(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
    tok: Option<&T>,
) -> fmt::Result {
    match tok {
        Some(tok) => fmt_token(tok, f),
        None => write!(f, "end of input"),
    }
}
