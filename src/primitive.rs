use super::*;

/// See [`end`].
pub struct End<E>(PhantomData<E>);

impl<E> Clone for End<E> {
    fn clone(&self) -> Self { Self(PhantomData) }
}

impl<I: Clone, E: Error<I>> Parser<I, ()> for End<E> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<((), Option<E>), E>) {
        match stream.peek_token() {
            None => (0, Ok(((), None))),
            x => {
                let x = x.cloned();
                (0, Err(E::expected_token_found(stream.peek_span(), Vec::new(), x)))
            },
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

impl<I: Clone + PartialEq, E: Error<I>> Parser<I, I> for Just<I, E> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<(I, Option<E>), E>) {
        match stream.peek_token() {
            Some(x) if x == &self.0 => (1, Ok((stream.next().unwrap(), None))),
            x => {
                let x = x.cloned();
                (0, Err(E::expected_token_found(stream.peek_span(), vec![self.0.clone()], x)))
            },
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

impl<I: Clone + PartialEq, E: Error<I>> Parser<I, ()> for Seq<I, E> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<((), Option<E>), E>) {
        let mut n = 0;
        for expected in &self.0 {
            match stream.peek_token() {
                Some(x) if x == expected => {
                    n += 1;
                    stream.next().unwrap();
                },
                x => {
                    let x = x.cloned();
                    return (n, Err(E::expected_token_found(stream.peek_span(), vec![expected.clone()], x)));
                },
            }
        }
        (n, Ok(((), None)))
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

impl<I: Clone + PartialEq, E: Error<I>> Parser<I, I> for OneOf<I, E> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<(I, Option<E>), E>) {
        match stream.peek_token() {
            Some(x) if self.0.contains(x) => {
                (1, Ok((stream.next().unwrap(), None)))
            },
            x => {
                let x = x.cloned();
                (0, Err(E::expected_token_found(stream.peek_span(), self.0.clone(), x)))
            },
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

/// See [`none_of`].
pub struct NoneOf<I, E>(Vec<I>, PhantomData<E>);

impl<I: Clone, E> Clone for NoneOf<I, E> {
    fn clone(&self) -> Self { Self(self.0.clone(), PhantomData) }
}

impl<I: Clone + PartialEq, E: Error<I>> Parser<I, I> for NoneOf<I, E> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<(I, Option<E>), E>) {
        match stream.peek_token() {
            Some(x) if !self.0.contains(x) => {
                (1, Ok((stream.next().unwrap(), None)))
            },
            x => {
                let x = x.cloned();
                (0, Err(E::expected_token_found(stream.peek_span(), Vec::new(), x)))
            },
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

impl<I: Clone, F: Fn(&I) -> bool, E: Error<I>> Parser<I, I> for Filter<F, E> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<(I, Option<E>), E>) {
        match stream.peek_token() {
            Some(x) if (self.0)(x) => (1, Ok((stream.next().unwrap(), None))),
            x => {
                let x = x.cloned();
                (0, Err(E::expected_token_found(stream.peek_span(), Vec::new(), x)))
            },
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

impl<I: Clone, O, F: Fn(E::Span, I) -> Result<O, E>, E: Error<I>> Parser<I, O> for FilterMap<F, E> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<(O, Option<E>), E>) {
        match stream.peek() {
            Some((x, span)) => match (self.0)(span, x.clone()) {
                Ok(o) => {
                    stream.next().unwrap();
                    (1, Ok((o, None)))
                },
                Err(e) => (0, Err(e)),
            },
            x => {
                let x = x.map(|(x, _)| x.clone());
                (0, Err(E::expected_token_found(stream.peek_span(), Vec::new(), x)))
            },
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
pub fn filter_map<I, O, F: Fn(E::Span, I) -> Result<O, E>, E: Error<I>>(f: F) -> FilterMap<F, E> {
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
