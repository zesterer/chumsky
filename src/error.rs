use std::{
    fmt,
    cmp::Ord,
    ops::Range,
};

/// A trait representing a span over elements of a token stream
pub trait Span {
    /// A position that can be used to demarcate the bounds of this span.
    type Position: Ord;

    /// Get the start position of this span.
    fn start(&self) -> Self::Position;
    /// Get the (exclusive) end position of this span.
    fn end(&self) -> Self::Position;
    /// Find the span that is the closest fit around two spans as possible.
    ///
    /// # Panics
    ///
    /// This function is permitted to panic if the first comes after the last.
    fn union(self, other: Self) -> Self;
    /// Find the span that fits between two spans but does not intersect with either.
    ///
    /// # Panics
    ///
    /// This function is permitted to panic if the spans intersect or the first comes after the last.
    fn inner(self, other: Self) -> Self;

    /// Return a value that allows displaying this span.
    ///
    /// Note that this function exists to work around certain implementation details and is highly likely to be removed
    /// in the future. If possible, implement [`std::fmt::Display`] for your span type too.
    fn display(&self) -> Box<dyn fmt::Display + '_>;
}

impl<T: Ord + Clone + fmt::Display> Span for Range<T> {
    type Position = T;

    fn start(&self) -> Self::Position { self.start.clone() }
    fn end(&self) -> Self::Position { self.end.clone() }
    fn union(self, other: Self) -> Self {
        self.start.min(other.start)..self.end.max(other.end)
    }
    fn inner(self, other: Self) -> Self {
        if self.end <= other.start {
            self.end.clone()..other.start.clone()
        } else {
            panic!("Spans intersect or are incorrectly ordered");
        }
    }
    fn display(&self) -> Box<dyn fmt::Display + '_> { Box::new(format!("{}..{}", self.start, self.end)) }
}

/// A trait that describes parser error types.
pub trait Error<I>: Sized {
    /// The type of spans to be used in the error.
    type Span: Span; // TODO: Default to = Range<usize>;

    /// The label used to describe tokens or a token pattern in error messages.
    ///
    /// Commonly, this type has a way to represent both *specific* tokens and groups of tokens like 'expressions' or
    /// 'statements'.
    type Pattern; // TODO: Default to = I;

    /// The primary span that the error originated at, if one exists.
    fn span(&self) -> Option<Self::Span>;

    /// Create a new error describing a conflict between expected tokens and that which was actually found.
    ///
    /// Using a `None` as `found` indicates that the end of input was reached, but was not expected.
    fn expected_token_found(span: Option<Self::Span>, expected: Vec<I>, found: Option<I>) -> Self;

    /// Create a new error describing a conflict between an expected label and that the token that was actually found.
    ///
    /// Using a `None` as `found` indicates that the end of input was reached, but was not expected.
    fn expected_label_found<L: Into<Self::Pattern>>(span: Option<Self::Span>, expected: L, found: Option<I>) -> Self {
        Self::expected_token_found(span, Vec::new(), found).into_labelled(expected)
    }

    /// Alter the error message to indicate that the given labelled pattern was expected.
    fn into_labelled<L: Into<Self::Pattern>>(self, label: L) -> Self;

    /// Merge two errors together, combining their elements.
    ///
    /// Note that when the errors originate from two different locations in the token stream (i.e: their span
    /// [`Span::end`] differs), the error error with the latest position should be preferred. When merging errors,
    /// unresolvable differences should favour `self`.
    fn merge(self, other: Self) -> Self {
        if let Some((a, b)) = self.span().zip(other.span()) {
            if a.end() < b.end() {
                other
            } else {
                self
            }
        } else {
            self
        }
    }
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

/// A simple default error type that provides minimal functionality.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Simple<I, S = Range<usize>> {
    span: Option<S>,
    expected: Vec<SimplePattern<I>>,
    found: Option<I>,
}

impl<I, S> Simple<I, S> {
    /// Returns an iterator over possible expected patterns.
    pub fn expected(&self) -> impl ExactSizeIterator<Item = &SimplePattern<I>> + '_ { self.expected.iter() }

    /// Returns the token, if any, that was found instead of an expected pattern.
    pub fn found(&self) -> Option<&I> { self.found.as_ref() }
}

impl<I, S: Span + Clone> Error<I> for Simple<I, S> {
    type Span = S;
    type Pattern = SimplePattern<I>;

    fn span(&self) -> Option<Self::Span> { self.span.clone() }

    fn expected_token_found(span: Option<Self::Span>, expected: Vec<I>, found: Option<I>) -> Self {
        Self {
            span,
            expected: expected
                .into_iter()
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
        let end = self.span().map_or(0, |span| span.end());
        let other_end = other.span().map_or(0, |span| span.end());

        if end > other_end {
            other
        } else if end < other_end {
            self
        } else {
            self.expected.append(&mut other.expected);
            self
        }
    }
}

impl<I: fmt::Display, S: Span> fmt::Display for Simple<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(found) = &self.found {
            write!(f, "found '{}' ", found)?;
        } else {
            write!(f, "the input ended ")?;
        }

        if let Some(span) = &self.span {
            write!(f, "at {} ", span.display())?;
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
impl<I: fmt::Debug + fmt::Display, S: Span + fmt::Debug> std::error::Error for Simple<I, S> {}
