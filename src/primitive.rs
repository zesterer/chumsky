use super::*;

/// See [`custom`].
pub struct Custom<F, E>(F, PhantomData<E>);

impl<F: Copy, E> Copy for Custom<F, E> {}
impl<F: Clone, E> Clone for Custom<F, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<I: Clone, O, F: Fn(&mut StreamOf<I, E>) -> PResult<I, O, E>, E: Error<I>> Parser<I, O>
    for Custom<F, E>
{
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, O, E> {
        (self.0)(stream)
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, O, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, O, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// A parser primitive that allows you to define your own custom parsers. In theory you shouldn't need to use this
/// unless you have particularly bizarre requirements, but it's a cleaner and more sustainable alternative to
/// implementing [`Parser`] by hand.
pub fn custom<F, E>(f: F) -> Custom<F, E> {
    Custom(f, PhantomData)
}

/// See [`end`].
pub struct End<E>(PhantomData<E>);

impl<E> Clone for End<E> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<I: Clone, E: Error<I>> Parser<I, ()> for End<E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, (), E> {
        match stream.next() {
            (_, _, None) => (Vec::new(), Ok(((), None))),
            (at, span, found) => (
                Vec::new(),
                Err(Located::at(
                    at,
                    E::expected_input_found(span, Vec::new(), found),
                )),
            ),
        }
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, (), E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, (), E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// A parser that accepts only the end of input.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// assert_eq!(end::<Cheap<char>>().parse(""), Ok(()));
/// assert!(end::<Cheap<char>>().parse("hello").is_err());
/// ```
pub fn end<E>() -> End<E> {
    End(PhantomData)
}

/// See [`just`].
pub struct Just<I, E>(I, PhantomData<E>);

impl<I: Copy, E> Copy for Just<I, E> {}
impl<I: Clone, E> Clone for Just<I, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<I: Clone + PartialEq, E: Error<I>> Parser<I, I> for Just<I, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, I, E> {
        match stream.next() {
            (_, _, Some(tok)) if tok == self.0 => (Vec::new(), Ok((tok, None))),
            (at, span, found) => (
                Vec::new(),
                Err(Located::at(
                    at,
                    E::expected_input_found(span, Some(self.0.clone()), found),
                )),
            ),
        }
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, I, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, I, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// A parser that accepts only the given input.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let question = just::<_, Cheap<char>>('?');
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
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<I: Clone + PartialEq, E: Error<I>> Parser<I, ()> for Seq<I, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, (), E> {
        for expected in &self.0 {
            match stream.next() {
                (_, _, Some(tok)) if &tok == expected => {}
                (at, span, found) => {
                    return (
                        Vec::new(),
                        Err(Located::at(
                            at,
                            E::expected_input_found(span, Some(expected.clone()), found),
                        )),
                    )
                }
            }
        }

        (Vec::new(), Ok(((), None)))
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, (), E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, (), E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// A parser that accepts only a sequence of specific inputs.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let hello = seq::<_, _, Cheap<char>>("Hello".chars());
///
/// assert_eq!(hello.parse("Hello"), Ok(()));
/// assert_eq!(hello.parse("Hello, world!"), Ok(()));
/// assert!(hello.parse("Goodbye").is_err());
///
/// let onetwothree = seq::<_, _, Cheap<i32>>([1, 2, 3]);
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
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<I: Clone + PartialEq, E: Error<I>> Parser<I, I> for OneOf<I, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, I, E> {
        match stream.next() {
            (_, _, Some(tok)) if self.0.contains(&tok) => (Vec::new(), Ok((tok.clone(), None))),
            (at, span, found) => {
                return (
                    Vec::new(),
                    Err(Located::at(
                        at,
                        E::expected_input_found(span, self.0.clone(), found),
                    )),
                )
            }
        }
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, I, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, I, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// A parser that accepts one of a sequence of specific inputs.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let digits = one_of::<_, _, Cheap<char>>("0123456789".chars())
///     .repeated().at_least(1)
///     .then_ignore(end())
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
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<I: Clone, E: Error<I>> Parser<I, ()> for Empty<E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        _: &mut StreamOf<I, E>,
    ) -> PResult<I, (), E> {
        (Vec::new(), Ok(((), None)))
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, (), E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, (), E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// A parser that parses no inputs.
pub fn empty<E>() -> Empty<E> {
    Empty(PhantomData)
}

/// See [`none_of`].
pub struct NoneOf<I, E>(Vec<I>, PhantomData<E>);

impl<I: Clone, E> Clone for NoneOf<I, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<I: Clone + PartialEq, E: Error<I>> Parser<I, I> for NoneOf<I, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, I, E> {
        match stream.next() {
            (_, _, Some(tok)) if !self.0.contains(&tok) => (Vec::new(), Ok((tok.clone(), None))),
            (at, span, found) => {
                return (
                    Vec::new(),
                    Err(Located::at(
                        at,
                        E::expected_input_found(span, Vec::new(), found),
                    )),
                )
            }
        }
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, I, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, I, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// A parser that accepts any input that is *not* in a sequence of specific inputs.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let string = one_of::<_, _, Cheap<char>>("\"'".chars())
///     .ignore_then(none_of("\"'".chars()).repeated())
///     .then_ignore(one_of("\"'".chars()))
///     .then_ignore(end())
///     .collect::<String>();
///
/// assert_eq!(string.parse("'hello'"), Ok("hello".to_string()));
/// assert_eq!(string.parse("\"world\""), Ok("world".to_string()));
/// assert!(string.parse("\"421!53").is_err());
/// ```
pub fn none_of<I: Clone + PartialEq, Iter: IntoIterator<Item = I>, E>(xs: Iter) -> NoneOf<I, E> {
    NoneOf(xs.into_iter().collect(), PhantomData)
}

/// See [`take_until`].
#[derive(Copy, Clone)]
pub struct TakeUntil<A>(A);

impl<I: Clone, O, A: Parser<I, O>> Parser<I, (Vec<I>, O)> for TakeUntil<A> {
    type Error = A::Error;

    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<I, A::Error>,
    ) -> PResult<I, (Vec<I>, O), A::Error> {
        let mut outputs = Vec::new();
        let mut alt = None;

        loop {
            let (errors, err) = match stream.try_parse(|stream| {
                #[allow(deprecated)]
                self.0.parse_inner(debugger, stream)
            }) {
                (errors, Ok((out, a_alt))) => {
                    break (errors, Ok(((outputs, out), merge_alts(alt, a_alt))))
                }
                (errors, Err(err)) => (errors, err),
            };

            match stream.next() {
                (_, _, Some(tok)) => outputs.push(tok),
                (_, _, None) => break (errors, Err(err)),
            }

            alt = merge_alts(alt.take(), Some(err));
        }
    }

    fn parse_inner_verbose(
        &self,
        d: &mut Verbose,
        s: &mut StreamOf<I, A::Error>,
    ) -> PResult<I, (Vec<I>, O), A::Error> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(
        &self,
        d: &mut Silent,
        s: &mut StreamOf<I, A::Error>,
    ) -> PResult<I, (Vec<I>, O), A::Error> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// A parser that accepts any number of inputs until a terminating pattern is reached.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let single_line = seq::<_, _, Simple<char>>("//".chars())
///     .then(take_until(text::newline()));
///
/// let multi_line = seq::<_, _, Simple<char>>("/*".chars())
///     .then(take_until(seq("*/".chars())));
///
/// let comment = single_line.or(multi_line);
///
/// let tokens = text::ident()
///     .padded()
///     .padded_by(comment
///         .padded()
///         .repeated())
///     .repeated();
///
/// assert_eq!(tokens.parse(r#"
///     // These tokens...
///     these are
///     /*
///         ...have some
///         multi-line...
///     */
///     // ...and single-line...
///     tokens
///     // ...comments between them
/// "#), Ok(vec!["these".to_string(), "are".to_string(), "tokens".to_string()]));
/// ```
pub fn take_until<A>(until: A) -> TakeUntil<A> {
    TakeUntil(until)
}

/// See [`filter`].
pub struct Filter<F, E>(F, PhantomData<E>);

impl<F: Copy, E> Copy for Filter<F, E> {}
impl<F: Clone, E> Clone for Filter<F, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<I: Clone, F: Fn(&I) -> bool, E: Error<I>> Parser<I, I> for Filter<F, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, I, E> {
        match stream.next() {
            (_, _, Some(tok)) if (self.0)(&tok) => (Vec::new(), Ok((tok, None))),
            (at, span, found) => (
                Vec::new(),
                Err(Located::at(
                    at,
                    E::expected_input_found(span, Vec::new(), found),
                )),
            ),
        }
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, I, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, I, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// A parser that accepts only inputs that match the given predicate.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let lowercase = filter::<_, _, Cheap<char>>(char::is_ascii_lowercase)
///     .repeated().at_least(1)
///     .then_ignore(end())
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
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<I: Clone, O, F: Fn(E::Span, I) -> Result<O, E>, E: Error<I>> Parser<I, O> for FilterMap<F, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, O, E> {
        let (at, span, tok) = stream.next();
        match tok.map(|tok| (self.0)(span.clone(), tok)) {
            Some(Ok(tok)) => (Vec::new(), Ok((tok, None))),
            Some(Err(err)) => (Vec::new(), Err(Located::at(at, err))),
            None => (
                Vec::new(),
                Err(Located::at(
                    at,
                    E::expected_input_found(span, Vec::new(), None),
                )),
            ),
        }
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, O, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, O, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// A parser that accepts a input and tests it against the given fallible function.
///
/// This function allows integration with custom error types to allow for custom parser errors.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let numeral = filter_map(|span, c: char| match c.to_digit(10) {
///     Some(x) => Ok(x),
///     None => Err(Simple::custom(span, format!("'{}' is not a digit", c))),
/// });
///
/// assert_eq!(numeral.parse("3"), Ok(3));
/// assert_eq!(numeral.parse("7"), Ok(7));
/// assert_eq!(numeral.parse("f"), Err(vec![Simple::custom(0..1, "'f' is not a digit")]));
/// ```
pub fn filter_map<I, O, F: Fn(E::Span, I) -> Result<O, E>, E: Error<I>>(f: F) -> FilterMap<F, E> {
    FilterMap(f, PhantomData)
}

/// See [`any`].
pub type Any<I, E> = Filter<fn(&I) -> bool, E>;

/// A parser that accepts any input (but not the end of input).
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let any = any::<char, Cheap<char>>();
///
/// assert_eq!(any.parse("a"), Ok('a'));
/// assert_eq!(any.parse("7"), Ok('7'));
/// assert_eq!(any.parse("\t"), Ok('\t'));
/// assert!(any.parse("").is_err());
/// ```
pub fn any<I, E>() -> Any<I, E> {
    Filter(|_| true, PhantomData)
}
