use super::*;

/// See [`end`].
pub struct End<E>(PhantomData<E>);

impl<E> Clone for End<E> {
    fn clone(&self) -> Self { Self(PhantomData) }
}

impl<I: Clone, E: Error<Token = I>> Parser<I, ()> for End<E> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<(), Self::Error> {
        match stream.next() {
            (_, None) => (Vec::new(), Ok(((), None))),
            (at, found) => (Vec::new(), Err(Located::at(at, E::expected_token_found(todo!(), Vec::new(), found)))),
        }
    }
}

/// A parser that accepts only the end of input.
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
///
/// assert_eq!(end::<Simple<char>>().parse(""), Ok(()));
/// assert!(end::<Simple<char>>().parse("hello").is_err());
/// ```
pub fn end<E>() -> End<E> {
    End(PhantomData)
}

/// See [`just`].
pub struct Just<I, E>(I, PhantomData<E>);

impl<I: Copy, E> Copy for Just<I, E> {}
impl<I: Clone, E> Clone for Just<I, E> {
    fn clone(&self) -> Self { Self(self.0.clone(), PhantomData) }
}

impl<I: Clone + PartialEq, E: Error<Token = I>> Parser<I, I> for Just<I, E> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<I, Self::Error> {
        match stream.next() {
            (_, Some(tok)) if tok == self.0 => (Vec::new(), Ok((tok, None))),
            (at, found) => (Vec::new(), Err(Located::at(at, E::expected_token_found(todo!(), vec![self.0.clone()], found)))),
        }
    }
}

/// A parser that accepts only the given token.
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
///
/// let question = just::<_, Simple<char>>('?');
///
/// assert_eq!(question.parse("?"), Ok('?'));
/// assert!(question.parse("!").is_err());
/// // This works because parsers do not eagerly consume input, so the '!' is not parsed
/// assert_eq!(question.parse("?!"), Ok('?'));
/// // This fails because the parser expects an end to the input after the '?'
/// assert!(question.then(end()).parse("?!").is_err());
/// ```
pub fn just<I: Clone + PartialEq, E>(x: I) -> Just<I, E> {
    Just(x, PhantomData)
}

/// See [`seq`].
pub struct Seq<I, E>(Vec<I>, PhantomData<E>);

impl<I: Clone, E> Clone for Seq<I, E> {
    fn clone(&self) -> Self { Self(self.0.clone(), PhantomData) }
}

impl<I: Clone + PartialEq, E: Error<Token = I>> Parser<I, ()> for Seq<I, E> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<(), Self::Error> {
        for expected in &self.0 {
            match stream.next() {
                (_, Some(tok)) if &tok == expected => {},
                (at, found) => return (Vec::new(), Err(Located::at(at, E::expected_token_found(todo!(), vec![expected.clone()], found)))),
            }
        }

        (Vec::new(), Ok(((), None)))
    }
}

/// A parser that accepts only a sequence of specific tokens.
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
///
/// let hello = seq::<_, _, Simple<char>>("Hello".chars());
///
/// assert_eq!(hello.parse("Hello"), Ok(()));
/// assert_eq!(hello.parse("Hello, world!"), Ok(()));
/// assert!(hello.parse("Goodbye").is_err());
///
/// let onetwothree = seq::<_, _, Simple<i32>>([1, 2, 3]);
///
/// assert_eq!(onetwothree.parse([1, 2, 3]), Ok(()));
/// assert_eq!(onetwothree.parse([1, 2, 3, 4, 5]), Ok(()));
/// assert!(onetwothree.parse([2, 1, 3]).is_err());
/// ```
pub fn seq<I: Clone + PartialEq, Iter: IntoIterator<Item = I>, E>(xs: Iter) -> Seq<I, E> {
    Seq(xs.into_iter().collect(), PhantomData)
}

/// See [`one_of`].
pub struct OneOf<I, E>(Vec<I>, PhantomData<E>);

impl<I: Clone, E> Clone for OneOf<I, E> {
    fn clone(&self) -> Self { Self(self.0.clone(), PhantomData) }
}

impl<I: Clone + PartialEq, E: Error<Token = I>> Parser<I, I> for OneOf<I, E> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<I, Self::Error> {
        match stream.next() {
            (_, Some(tok)) if self.0.contains(&tok) => (Vec::new(), Ok((tok.clone(), None))),
            (at, found) => return (Vec::new(), Err(Located::at(at, E::expected_token_found(todo!(), self.0.clone(), found)))),
        }
    }
}

/// A parser that accepts one of a sequence of specific tokens.
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
///
/// let digits = one_of::<_, _, Simple<char>>("0123456789".chars())
///     .repeated_at_least(1)
///     .padded_by(end())
///     .collect::<String>();
///
/// assert_eq!(digits.parse("48791"), Ok("48791".to_string()));
/// assert!(digits.parse("421!53").is_err());
/// ```
pub fn one_of<I: Clone + PartialEq, Iter: IntoIterator<Item = I>, E>(xs: Iter) -> OneOf<I, E> {
    OneOf(xs.into_iter().collect(), PhantomData)
}

/// See [`empty`].
pub struct Empty<E>(PhantomData<E>);

impl<E> Clone for Empty<E> {
    fn clone(&self) -> Self { Self(PhantomData) }
}

impl<I: Clone, E: Error<Token = I>> Parser<I, ()> for Empty<E> {
    type Error = E;

    fn parse_inner(&self, _: &mut Stream<I>) -> PResult<(), Self::Error> {
        (Vec::new(), Ok(((), None)))
    }
}

/// A parser that parses no tokens.
pub fn empty<E>() -> Empty<E> {
    Empty(PhantomData)
}

/// See [`none_of`].
pub struct NoneOf<I, E>(Vec<I>, PhantomData<E>);

impl<I: Clone, E> Clone for NoneOf<I, E> {
    fn clone(&self) -> Self { Self(self.0.clone(), PhantomData) }
}

impl<I: Clone + PartialEq, E: Error<Token = I>> Parser<I, I> for NoneOf<I, E> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<I, Self::Error> {
        match stream.next() {
            (_, Some(tok)) if !self.0.contains(&tok) => (Vec::new(), Ok((tok.clone(), None))),
            (at, found) => return (Vec::new(), Err(Located::at(at, E::expected_token_found(todo!(), Vec::new(), found)))),
        }
    }
}

/// A parser that accepts any token that is *not* in a sequence of specific tokens.
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
///
/// let string = one_of::<_, _, Simple<char>>("\"'".chars())
///     .padding_for(none_of("\"'".chars()).repeated())
///     .padded_by(one_of("\"'".chars()))
///     .padded_by(end())
///     .collect::<String>();
///
/// assert_eq!(string.parse("'hello'"), Ok("hello".to_string()));
/// assert_eq!(string.parse("\"world\""), Ok("world".to_string()));
/// assert!(string.parse("\"421!53").is_err());
/// ```
pub fn none_of<I: Clone + PartialEq, Iter: IntoIterator<Item = I>, E>(xs: Iter) -> NoneOf<I, E> {
    NoneOf(xs.into_iter().collect(), PhantomData)
}

/// See [`filter`].
pub struct Filter<F, E>(F, PhantomData<E>);

impl<F: Copy, E> Copy for Filter<F, E> {}
impl<F: Clone, E> Clone for Filter<F, E> {
    fn clone(&self) -> Self { Self(self.0.clone(), PhantomData) }
}

impl<I: Clone, F: Fn(&I) -> bool, E: Error<Token = I>> Parser<I, I> for Filter<F, E> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<I, Self::Error> {
        match stream.next() {
            (_, Some(tok)) if (self.0)(&tok) => (Vec::new(), Ok((tok, None))),
            (at, found) => (Vec::new(), Err(Located::at(at, E::expected_token_found(todo!(), Vec::new(), found)))),
        }
    }
}

/// A parser that accepts only tokens that match the given predicate.
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
///
/// let lowercase = filter::<_, _, Simple<char>>(char::is_ascii_lowercase)
///     .repeated_at_least(1)
///     .padded_by(end())
///     .collect::<String>();
///
/// assert_eq!(lowercase.parse("hello"), Ok("hello".to_string()));
/// assert!(lowercase.parse("Hello").is_err());
/// ```
pub fn filter<I, F: Fn(&I) -> bool, E>(f: F) -> Filter<F, E> {
    Filter(f, PhantomData)
}

/// See [`filter_map`].
pub struct FilterMap<F, E>(F, PhantomData<E>);

impl<F: Copy, E> Copy for FilterMap<F, E> {}
impl<F: Clone, E> Clone for FilterMap<F, E> {
    fn clone(&self) -> Self { Self(self.0.clone(), PhantomData) }
}

impl<I: Clone, O, F: Fn(E::Span, I) -> Result<O, E>, E: Error<Token = I>> Parser<I, O> for FilterMap<F, E> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<O, Self::Error> {
        let (at, tok) = stream.next();
        let span = todo!();
        match tok.map(|tok| (self.0)(span, tok)) {
            Some(Ok(tok)) => (Vec::new(), Ok((tok, None))),
            Some(Err(err)) => (Vec::new(), Err(Located::at(at, err))),
            None => (Vec::new(), Err(Located::at(at, E::expected_token_found(todo!(), Vec::new(), None)))),
        }
    }
}

/// A parser that accepts a token and tests it against the given fallible function.
///
/// This function allows integration with custom error types to allow for custom parser errors.
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
/// use std::ops::Range;
///
/// // A custom error type
/// #[derive(Debug, PartialEq)]
/// enum Custom {
///     ExpectedFound(Option<Range<usize>>, Vec<char>, Option<char>),
///     NotADigit(Option<Range<usize>>, char),
/// }
///
/// impl chumsky::Error<char> for Custom {
///     type Span = Range<usize>;
///     type Pattern = char;
///
///     fn span(&self) -> Option<Self::Span> {
///         match self {
///             Self::ExpectedFound(span, _, _) => span.clone(),
///             Self::NotADigit(span, _) => span.clone(),
///         }
///     }
///
///     fn expected_token_found(span: Option<Range<usize>>, expected: Vec<char>, found: Option<char>) -> Self {
///         Self::ExpectedFound(span, expected, found)
///     }
///
///     fn into_labelled<L: Into<Self::Pattern>>(mut self, label: L) -> Self {
///         if let Self::ExpectedFound(_, expected, _) = &mut self {
///             *expected = vec![label.into()];
///         }
///         self
///     }
/// }
///
/// let numeral = filter_map(|span, c: char| match c.to_digit(10) {
///     Some(x) => Ok(x),
///     None => Err(Custom::NotADigit(Some(span), c)),
/// });
///
/// assert_eq!(numeral.parse("3"), Ok(3));
/// assert_eq!(numeral.parse("7"), Ok(7));
/// assert_eq!(numeral.parse("f"), Err(vec![Custom::NotADigit(Some(0..1), 'f')]));
/// ```
pub fn filter_map<I, O, F: Fn(E::Span, I) -> Result<O, E>, E: Error<Token = I>>(f: F) -> FilterMap<F, E> {
    FilterMap(f, PhantomData)
}

/// See [`any`].
pub type Any<I, E> = Filter<fn(&I) -> bool, E>;

/// A parser that accepts any token (but not the end of input).
///
/// # Examples
///
/// ```
/// use chumsky::prelude::*;
///
/// let any = any::<char, Simple<char>>();
///
/// assert_eq!(any.parse("a"), Ok('a'));
/// assert_eq!(any.parse("7"), Ok('7'));
/// assert_eq!(any.parse("🤖"), Ok('🤖'));
/// assert!(any.parse("").is_err());
/// ```
pub fn any<I, E>() -> Any<I, E> {
    Filter(|_| true, PhantomData)
}
