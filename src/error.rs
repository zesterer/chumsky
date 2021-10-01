use super::*;

/// A trait that describes parser error types.
pub trait Error: Sized {
    type Token;
    /// The type of spans to be used in the error.
    type Span: Span; // TODO: Default to = Range<usize>;

    /// The label used to describe tokens or a token pattern in error messages.
    ///
    /// Commonly, this type has a way to represent both *specific* tokens and groups of tokens like 'expressions' or
    /// 'statements'.
    type Pattern; // TODO: Default to = I;

    /// The primary span that the error originated at, if one exists.
    fn span(&self) -> Self::Span;

    /// Create a new error describing a conflict between expected tokens and that which was actually found.
    ///
    /// Using a `None` as `found` indicates that the end of input was reached, but was not expected.
    fn expected_token_found<Iter: IntoIterator<Item = Self::Token>>(span: Self::Span, expected: Iter, found: Option<Self::Token>) -> Self;

    fn unclosed_delimiter(start_span: Self::Span, start: Self::Token, span: Self::Span, expected: Self::Token, found: Option<Self::Token>) -> Self;

    /// Create a new error describing a conflict between an expected label and that the token that was actually found.
    ///
    /// Using a `None` as `found` indicates that the end of input was reached, but was not expected.
    fn expected_label_found<L: Into<Self::Pattern>>(span: Self::Span, expected: L, found: Option<Self::Token>) -> Self {
        Self::expected_token_found(span, Vec::new(), found).into_labelled(expected)
    }

    /// Alter the error message to indicate that the given labelled pattern was expected.
    fn into_labelled<L: Into<Self::Pattern>>(self, label: L) -> Self;

    /// Merge two errors that point to the same token together, combining their information.
    fn merge(self, other: Self) -> Self;

    // fn debug(&self) -> &dyn fmt::Debug;
}

/// A simple default token pattern that allows describing tokens and token patterns in error messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimplePattern<I> {
    /// A pattern with the given name was expected.
    Labelled(&'static str),
    /// A specific token was expected.
    Token(I),
}

impl<I> From<&'static str> for SimplePattern<I> {
    fn from(s: &'static str) -> Self { Self::Labelled(s) }
}

impl<I: fmt::Display> fmt::Display for SimplePattern<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Labelled(s) => write!(f, "{}", s),
            Self::Token(x) => write!(f, "'{}'", x),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimpleReason<I, S> {
    Unclosed(S, I),
}

/// A simple default error type that tracks error spans, expected patterns, and the token found at an error site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Simple<I, S = Range<usize>> {
    span: S,
    reason: Option<SimpleReason<I, S>>,
    expected: Vec<SimplePattern<I>>,
    found: Option<I>,
}

impl<I, S> Simple<I, S> {
    /// Returns an iterator over possible expected patterns.
    pub fn expected(&self) -> impl ExactSizeIterator<Item = &SimplePattern<I>> + '_ { self.expected.iter() }

    /// Returns the token, if any, that was found instead of an expected pattern.
    pub fn found(&self) -> Option<&I> { self.found.as_ref() }

    pub fn reason(&self) -> Option<&SimpleReason<I, S>> { self.reason.as_ref() }

    pub fn map<U, F: FnMut(I) -> U>(self, mut f: F) -> Simple<U, S> {
        Simple {
            span: self.span,
            reason: match self.reason {
                Some(SimpleReason::Unclosed(span, tok)) => Some(SimpleReason::Unclosed(span, f(tok))),
                None => None,
            },
            expected: self.expected
                .into_iter()
                .map(|pat| match pat {
                    SimplePattern::Labelled(label) => SimplePattern::Labelled(label),
                    SimplePattern::Token(tok) => SimplePattern::Token(f(tok)),
                })
                .collect(),
            found: self.found.map(f),
        }
    }
}

impl<I: fmt::Debug, S: Span + Clone + fmt::Debug> Error for Simple<I, S> {
    type Token = I;
    type Span = S;
    type Pattern = SimplePattern<I>;

    fn span(&self) -> Self::Span { self.span.clone() }

    fn expected_token_found<Iter: IntoIterator<Item = Self::Token>>(span: Self::Span, expected: Iter, found: Option<Self::Token>) -> Self {
        Self {
            span,
            reason: None,
            expected: expected
                .into_iter()
                .map(SimplePattern::Token)
                .collect(),
            found,
        }
    }

    fn unclosed_delimiter(start_span: Self::Span, start: Self::Token, span: Self::Span, expected: Self::Token, found: Option<Self::Token>) -> Self {
        Self {
            span,
            reason: Some(SimpleReason::Unclosed(start_span, start)),
            expected: std::iter::once(expected)
                .map(SimplePattern::Token)
                .collect(),
            found,
        }
    }

    fn into_labelled<L: Into<Self::Pattern>>(mut self, label: L) -> Self {
        self.expected = vec![label.into()];
        self
    }

    fn merge(mut self, mut other: Self) -> Self {
        // TODO: Assert that `self.span == other.span` here?
        let reasons_match = self.reason.is_some() == other.reason.is_some();
        self.reason = self.reason.filter(|_| reasons_match);
        self.expected.append(&mut other.expected);
        self
    }

    // fn debug(&self) -> &dyn fmt::Debug { self }
}

impl<I: fmt::Display, S: Span + fmt::Display> fmt::Display for Simple<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(found) = &self.found {
            write!(f, "found '{}' ", found)?;
            write!(f, "at {} ", self.span)?;
        } else {
            write!(f, "the input ended ")?;
        }


        match self.expected.as_slice() {
            [] => write!(f, "but end of input was expected")?,
            [expected] => write!(f, "but {} was expected", expected)?,
            [_, ..] => write!(f, "but one of {} was expected", self.expected
                .iter()
                .map(|expected| expected.to_string())
                .collect::<Vec<_>>()
                .join(", "))?,
        }

        Ok(())
    }
}

impl<I: fmt::Debug + fmt::Display, S: Span + fmt::Display + fmt::Debug> std::error::Error for Simple<I, S> {}

/// A minimal error type that tracks only the error span.
#[derive(Clone, Debug)]
pub struct OnlySpan<I, S = Range<usize>> {
    span: S,
    phantom: PhantomData<I>,
}

impl<I: fmt::Debug, S: Span + Clone + fmt::Debug> Error for OnlySpan<I, S> {
    type Token = I;
    type Span = S;
    type Pattern = SimplePattern<I>;

    fn span(&self) -> Self::Span { self.span.clone() }

    fn expected_token_found<Iter: IntoIterator<Item = Self::Token>>(span: Self::Span, _: Iter, _: Option<Self::Token>) -> Self {
        Self { span, phantom: PhantomData }
    }

    fn unclosed_delimiter(_: Self::Span, _: Self::Token, span: Self::Span, _: Self::Token, _: Option<Self::Token>) -> Self {
        Self { span, phantom: PhantomData }
    }

    fn into_labelled<L: Into<Self::Pattern>>(self, _: L) -> Self { self }

    fn merge(self, _: Self) -> Self { self }

    // fn debug(&self) -> &dyn fmt::Debug { self }
}
