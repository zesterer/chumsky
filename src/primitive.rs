use super::*;

/// See [`end`].
pub struct End<E>(PhantomData<E>);

impl<E> Clone for End<E> {
    fn clone(&self) -> Self { Self(PhantomData) }
}

impl<I: Clone, E: Error<I>> Parser<I, ()> for End<E> {
    type Error = E;

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<((), Option<E>), E>) where Self: Sized {
        match stream.peek() {
            None => (0, Ok(((), None))),
            x => {
                let x = x.cloned();
                (0, Err(E::expected_found(stream.position(), Vec::new(), x)))
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
/// assert_eq!(end::<Simple<char>>().parse("".chars()), Ok(()));
/// assert!(end::<Simple<char>>().parse("hello".chars()).is_err());
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

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<(I, Option<E>), E>) where Self: Sized {
        match stream.peek() {
            Some(x) if x == &self.0 => (1, Ok((stream.next().unwrap(), None))),
            x => {
                let x = x.cloned();
                (0, Err(E::expected_found(stream.position(), vec![self.0.clone()], x)))
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
/// assert_eq!(question.parse("?".chars()), Ok('?'));
/// assert!(question.parse("!".chars()).is_err());
/// // This works because parsers do not eagerly consume input, so the '!' is not parsed
/// assert_eq!(question.parse("?!".chars()), Ok('?'));
/// // This fails because the parser expects an end to the input after the '?'
/// assert!(question.then(end()).parse("?!".chars()).is_err());
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

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<((), Option<E>), E>) where Self: Sized {
        let mut n = 0;
        for expected in &self.0 {
            match stream.peek() {
                Some(x) if x == expected => {
                    n += 1;
                    stream.next().unwrap();
                },
                x => {
                    let x = x.cloned();
                    return (n, Err(E::expected_found(stream.position(), vec![expected.clone()], x)));
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
/// assert_eq!(hello.parse("Hello".chars()), Ok(()));
/// assert_eq!(hello.parse("Hello, world!".chars()), Ok(()));
/// assert!(hello.parse("Goodbye".chars()).is_err());
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

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<(I, Option<E>), E>) where Self: Sized {
        match stream.peek() {
            Some(x) if self.0.contains(x) => {
                (1, Ok((stream.next().unwrap(), None)))
            },
            x => {
                let x = x.cloned();
                (0, Err(E::expected_found(stream.position(), self.0.clone(), x)))
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
/// assert_eq!(digits.parse("48791".chars()), Ok("48791".to_string()));
/// assert!(digits.parse("421!53".chars()).is_err());
/// ```
pub fn one_of<I: Clone + PartialEq, Iter: IntoIterator<Item = I>, E>(xs: Iter) -> OneOf<I, E> {
    OneOf(xs.into_iter().collect(), PhantomData)
}

/// See [`filter`].
pub struct Filter<F, E>(F, PhantomData<E>);

impl<F: Copy, E> Copy for Filter<F, E> {}
impl<F: Clone, E> Clone for Filter<F, E> {
    fn clone(&self) -> Self { Self(self.0.clone(), PhantomData) }
}

impl<I: Clone, F: Fn(&I) -> bool, E: Error<I>> Parser<I, I> for Filter<F, E> {
    type Error = E;

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<(I, Option<E>), E>) where Self: Sized {
        match stream.peek() {
            Some(x) if (self.0)(x) => (1, Ok((stream.next().unwrap(), None))),
            x => {
                let x = x.cloned();
                (0, Err(E::expected_found(stream.position(), Vec::new(), x)))
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
/// assert_eq!(lowercase.parse("hello".chars()), Ok("hello".to_string()));
/// assert!(lowercase.parse("Hello".chars()).is_err());
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

impl<I: Clone, O, F: Fn(usize, I) -> Result<O, E>, E: Error<I>> Parser<I, O> for FilterMap<F, E> {
    type Error = E;

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, _: &mut Vec<Self::Error>) -> (usize, Result<(O, Option<E>), E>) where Self: Sized {
        let pos = stream.position();
        match stream.peek() {
            Some(x) => match (self.0)(pos, x.clone()) {
                Ok(o) => {
                    stream.next().unwrap();
                    (1, Ok((o, None)))
                },
                Err(e) => (0, Err(e)),
            },
            x => {
                let x = x.cloned();
                (0, Err(E::expected_found(stream.position(), Vec::new(), x)))
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
///
/// // A custom error type
/// #[derive(Debug, PartialEq)]
/// enum Custom {
///     ExpectedFound(usize, Vec<char>, Option<char>),
///     NotADigit(usize, char),
/// }
///
/// impl chumsky::Error<char> for Custom {
///     type Pattern = char;
///
///     fn position(&self) -> usize {
///         match self {
///             Self::ExpectedFound(p, _, _) => *p,
///             Self::NotADigit(p, _) => *p,
///         }
///     }
///
///     fn expected_found(pos: usize, expected: Vec<char>, found: Option<char>) -> Self {
///         Self::ExpectedFound(pos, expected, found)
///     }
///
///     fn label_expected<L: Into<Self::Pattern>>(mut self, label: L) -> Self {
///         if let Self::ExpectedFound(_, expected, _) = &mut self {
///             *expected = vec![label.into()];
///         }
///         self
///     }
/// }
///
/// let numeral = filter_map(|p, c: char| match c.to_digit(10) {
///     Some(x) => Ok(x),
///     None => Err(Custom::NotADigit(p, c)),
/// });
///
/// assert_eq!(numeral.parse("3".chars()), Ok(3));
/// assert_eq!(numeral.parse("7".chars()), Ok(7));
/// assert_eq!(numeral.parse("f".chars()), Err(vec![Custom::NotADigit(0, 'f')]));
/// ```
pub fn filter_map<I, O, F: Fn(usize, I) -> Result<O, E>, E>(f: F) -> FilterMap<F, E> {
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
/// assert_eq!(any.parse("a".chars()), Ok('a'));
/// assert_eq!(any.parse("7".chars()), Ok('7'));
/// assert_eq!(any.parse("🤖".chars()), Ok('🤖'));
/// assert!(any.parse("".chars()).is_err());
/// ```
pub fn any<I, E>() -> Any<I, E> {
    Filter(|_| true, PhantomData)
}
