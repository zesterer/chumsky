//! Parser primitives that accept specific token patterns.
//!
//! *“These creatures you call mice, you see, they are not quite as they appear. They are merely the protrusion into
//! our dimension of vastly hyperintelligent pandimensional beings.”*
//!
//! Chumsky parsers are created by combining together smaller parsers. Right at the bottom of the pile are the parser
//! primitives, a parser developer's bread & butter. Each of these primitives are very easy to understand in isolation,
//! usually only doing one thing.
//!
//! ## The Important Ones
//!
//! - [`just`]: parses a specific input or sequence of inputs
//! - [`filter`]: parses a single input, if the given filter function returns `true`
//! - [`end`]: parses the end of input (i.e: if there any more inputs, this parse fails)

use super::*;
use core::panic::Location;

/// See [`custom`].
#[must_use]
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

/// A parser primitive that allows you to define your own custom parsers.
///
/// In theory you shouldn't need to use this unless you have particularly bizarre requirements, but it's a cleaner and
/// more sustainable alternative to implementing [`Parser`] by hand.
///
/// The output type of this parser is determined by the parse result of the function.
pub fn custom<F, E>(f: F) -> Custom<F, E> {
    Custom(f, PhantomData)
}

/// See [`end`].
#[must_use]
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
                    E::expected_input_found(span, Some(None), found),
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
/// This parser is very useful when you wish to force a parser to consume *all* of the input. It is typically combined
/// with [`Parser::then_ignore`].
///
/// The output type of this parser is `()`.
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
/// assert_eq!(end::<Simple<char>>().parse(""), Ok(()));
/// assert!(end::<Simple<char>>().parse("hello").is_err());
/// ```
///
/// ```
/// # use chumsky::prelude::*;
/// let digits = text::digits::<_, Simple<char>>(10);
///
/// // This parser parses digits!
/// assert_eq!(digits.parse("1234"), Ok("1234".to_string()));
///
/// // However, parsers are lazy and do not consume trailing input.
/// // This can be inconvenient if we want to validate all of the input.
/// assert_eq!(digits.parse("1234AhasjADSJAlaDJKSDAK"), Ok("1234".to_string()));
///
/// // To fix this problem, we require that the end of input follows any successfully parsed input
/// let only_digits = digits.then_ignore(end());
///
/// // Now our parser correctly produces an error if any trailing input is found...
/// assert!(only_digits.parse("1234AhasjADSJAlaDJKSDAK").is_err());
/// // ...while still behaving correctly for inputs that only consist of valid patterns
/// assert_eq!(only_digits.parse("1234"), Ok("1234".to_string()));
/// ```
pub fn end<E>() -> End<E> {
    End(PhantomData)
}

mod private {
    pub trait Sealed<T> {}

    impl<T> Sealed<T> for T {}
    impl Sealed<char> for alloc::string::String {}
    impl<'a> Sealed<char> for &'a str {}
    impl<'a, T> Sealed<T> for &'a [T] {}
    impl<T, const N: usize> Sealed<T> for [T; N] {}
    impl<'a, T, const N: usize> Sealed<T> for &'a [T; N] {}
    impl<T> Sealed<T> for alloc::vec::Vec<T> {}
    impl<T> Sealed<T> for alloc::collections::LinkedList<T> {}
    impl<T> Sealed<T> for alloc::collections::VecDeque<T> {}
    impl<T> Sealed<T> for alloc::collections::BTreeSet<T> {}
    impl<T> Sealed<T> for alloc::collections::BinaryHeap<T> {}

    #[cfg(feature = "std")]
    impl<T> Sealed<T> for std::collections::HashSet<T> {}
    #[cfg(not(feature = "std"))]
    impl<T> Sealed<T> for hashbrown::HashSet<T> {}
}

/// A utility trait to abstract over container-like things.
///
/// This trait is sealed and an implementation detail - its internals should not be relied on by users.
pub trait Container<T>: private::Sealed<T> {
    /// An iterator over the items within this container, by value.
    type Iter: Iterator<Item = T>;
    /// Iterate over the elements of the container (using internal iteration because GATs are unstable).
    fn get_iter(&self) -> Self::Iter;
}

impl<T: Clone> Container<T> for T {
    type Iter = core::iter::Once<T>;
    fn get_iter(&self) -> Self::Iter {
        core::iter::once(self.clone())
    }
}

impl Container<char> for String {
    type Iter = alloc::vec::IntoIter<char>;
    fn get_iter(&self) -> Self::Iter {
        self.chars().collect::<Vec<_>>().into_iter()
    }
}

impl<'a> Container<char> for &'a str {
    type Iter = alloc::str::Chars<'a>;
    fn get_iter(&self) -> Self::Iter {
        self.chars()
    }
}

impl<'a, T: Clone> Container<T> for &'a [T] {
    type Iter = core::iter::Cloned<core::slice::Iter<'a, T>>;
    fn get_iter(&self) -> Self::Iter {
        self.iter().cloned()
    }
}

impl<'a, T: Clone, const N: usize> Container<T> for &'a [T; N] {
    type Iter = core::iter::Cloned<core::slice::Iter<'a, T>>;
    fn get_iter(&self) -> Self::Iter {
        self.iter().cloned()
    }
}

impl<T: Clone, const N: usize> Container<T> for [T; N] {
    type Iter = core::array::IntoIter<T, N>;
    fn get_iter(&self) -> Self::Iter {
        core::array::IntoIter::new(self.clone())
    }
}

impl<T: Clone> Container<T> for Vec<T> {
    type Iter = alloc::vec::IntoIter<T>;
    fn get_iter(&self) -> Self::Iter {
        self.clone().into_iter()
    }
}

impl<T: Clone> Container<T> for alloc::collections::LinkedList<T> {
    type Iter = alloc::collections::linked_list::IntoIter<T>;
    fn get_iter(&self) -> Self::Iter {
        self.clone().into_iter()
    }
}

impl<T: Clone> Container<T> for alloc::collections::VecDeque<T> {
    type Iter = alloc::collections::vec_deque::IntoIter<T>;
    fn get_iter(&self) -> Self::Iter {
        self.clone().into_iter()
    }
}

#[cfg(feature = "std")]
impl<T: Clone> Container<T> for std::collections::HashSet<T> {
    type Iter = std::collections::hash_set::IntoIter<T>;
    fn get_iter(&self) -> Self::Iter {
        self.clone().into_iter()
    }
}

#[cfg(not(feature = "std"))]
impl<T: Clone> Container<T> for hashbrown::HashSet<T> {
    type Iter = hashbrown::hash_set::IntoIter<T>;
    fn get_iter(&self) -> Self::Iter {
        self.clone().into_iter()
    }
}

impl<T: Clone> Container<T> for alloc::collections::BTreeSet<T> {
    type Iter = alloc::collections::btree_set::IntoIter<T>;
    fn get_iter(&self) -> Self::Iter {
        self.clone().into_iter()
    }
}

impl<T: Clone> Container<T> for alloc::collections::BinaryHeap<T> {
    type Iter = alloc::collections::binary_heap::IntoIter<T>;
    fn get_iter(&self) -> Self::Iter {
        self.clone().into_iter()
    }
}

/// A utility trait to abstract over linear and ordered container-like things, excluding things such
/// as sets and heaps.
///
/// This trait is sealed and an implementation detail - its internals should not be relied on by users.
pub trait OrderedContainer<T>: Container<T> {}

impl<T: Clone> OrderedContainer<T> for T {}
impl OrderedContainer<char> for String {}
impl<'a> OrderedContainer<char> for &'a str {}
impl<'a, T: Clone> OrderedContainer<T> for &'a [T] {}
impl<'a, T: Clone, const N: usize> OrderedContainer<T> for &'a [T; N] {}
impl<T: Clone, const N: usize> OrderedContainer<T> for [T; N] {}
impl<T: Clone> OrderedContainer<T> for Vec<T> {}
impl<T: Clone> OrderedContainer<T> for alloc::collections::LinkedList<T> {}
impl<T: Clone> OrderedContainer<T> for alloc::collections::VecDeque<T> {}

/// See [`just`].
#[must_use]
pub struct Just<I, C: OrderedContainer<I>, E>(C, PhantomData<(I, E)>);

impl<I, C: Copy + OrderedContainer<I>, E> Copy for Just<I, C, E> {}
impl<I, C: Clone + OrderedContainer<I>, E> Clone for Just<I, C, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<I: Clone + PartialEq, C: OrderedContainer<I> + Clone, E: Error<I>> Parser<I, C>
    for Just<I, C, E>
{
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, C, E> {
        for expected in self.0.get_iter() {
            match stream.next() {
                (_, _, Some(tok)) if tok == expected => {}
                (at, span, found) => {
                    return (
                        Vec::new(),
                        Err(Located::at(
                            at,
                            E::expected_input_found(span, Some(Some(expected)), found),
                        )),
                    )
                }
            }
        }

        (Vec::new(), Ok((self.0.clone(), None)))
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, C, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, C, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// A parser that accepts only the given input.
///
/// The output type of this parser is `C`, the input or sequence that was provided.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let question = just::<_, _, Cheap<char>>('?');
///
/// assert_eq!(question.parse("?"), Ok('?'));
/// assert!(question.parse("!").is_err());
/// // This works because parsers do not eagerly consume input, so the '!' is not parsed
/// assert_eq!(question.parse("?!"), Ok('?'));
/// // This fails because the parser expects an end to the input after the '?'
/// assert!(question.then(end()).parse("?!").is_err());
/// ```
pub fn just<I, C: OrderedContainer<I>, E: Error<I>>(inputs: C) -> Just<I, C, E> {
    Just(inputs, PhantomData)
}

/// See [`seq`].
#[must_use]
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
                            E::expected_input_found(span, Some(Some(expected.clone())), found),
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
/// The output type of this parser is `()`.
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
#[deprecated(
    since = "0.7.0",
    note = "Use `just` instead: it now works for many sequence-like types!"
)]
pub fn seq<I: Clone + PartialEq, Iter: IntoIterator<Item = I>, E>(xs: Iter) -> Seq<I, E> {
    Seq(xs.into_iter().collect(), PhantomData)
}

/// See [`one_of`].
#[must_use]
pub struct OneOf<I, C, E>(C, PhantomData<(I, E)>);

impl<I, C: Clone, E> Clone for OneOf<I, C, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<I: Clone + PartialEq, C: Container<I>, E: Error<I>> Parser<I, I> for OneOf<I, C, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, I, E> {
        match stream.next() {
            (_, _, Some(tok)) if self.0.get_iter().any(|not| not == tok) => {
                (Vec::new(), Ok((tok, None)))
            }
            (at, span, found) => (
                Vec::new(),
                Err(Located::at(
                    at,
                    E::expected_input_found(span, self.0.get_iter().map(Some), found),
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

/// A parser that accepts one of a sequence of specific inputs.
///
/// The output type of this parser is `I`, the input that was found.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let digits = one_of::<_, _, Cheap<char>>("0123456789")
///     .repeated().at_least(1)
///     .then_ignore(end())
///     .collect::<String>();
///
/// assert_eq!(digits.parse("48791"), Ok("48791".to_string()));
/// assert!(digits.parse("421!53").is_err());
/// ```
pub fn one_of<I, C: Container<I>, E: Error<I>>(inputs: C) -> OneOf<I, C, E> {
    OneOf(inputs, PhantomData)
}

/// See [`empty`].
#[must_use]
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
///
/// The output type of this parser is `()`.
pub fn empty<E>() -> Empty<E> {
    Empty(PhantomData)
}

/// See [`none_of`].
#[must_use]
pub struct NoneOf<I, C, E>(C, PhantomData<(I, E)>);

impl<I, C: Clone, E> Clone for NoneOf<I, C, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<I: Clone + PartialEq, C: Container<I>, E: Error<I>> Parser<I, I> for NoneOf<I, C, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, I, E> {
        match stream.next() {
            (_, _, Some(tok)) if self.0.get_iter().all(|not| not != tok) => {
                (Vec::new(), Ok((tok, None)))
            }
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

/// A parser that accepts any input that is *not* in a sequence of specific inputs.
///
/// The output type of this parser is `I`, the input that was found.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let string = one_of::<_, _, Cheap<char>>("\"'")
///     .ignore_then(none_of("\"'").repeated())
///     .then_ignore(one_of("\"'"))
///     .then_ignore(end())
///     .collect::<String>();
///
/// assert_eq!(string.parse("'hello'"), Ok("hello".to_string()));
/// assert_eq!(string.parse("\"world\""), Ok("world".to_string()));
/// assert!(string.parse("\"421!53").is_err());
/// ```
pub fn none_of<I, C: Container<I>, E: Error<I>>(inputs: C) -> NoneOf<I, C, E> {
    NoneOf(inputs, PhantomData)
}

/// See [`take_until`].
#[must_use]
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
/// The output type of this parser is `(Vec<I>, O)`, a combination of the preceding inputs and the output of the
/// final patterns.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
/// let single_line = just::<_, _, Simple<char>>("//")
///     .then(take_until(text::newline()))
///     .ignored();
///
/// let multi_line = just::<_, _, Simple<char>>("/*")
///     .then(take_until(just("*/")))
///     .ignored();
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
#[must_use]
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
/// The output type of this parser is `I`, the input that was found.
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
#[must_use]
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
/// Before using this function, consider whether the [`select`] macro would serve you better.
///
/// The output type of this parser is `I`, the input that was found.
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
/// The output type of this parser is `I`, the input that was found.
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

/// See [`fn@todo`].
#[must_use]
pub struct Todo<I, O, E>(&'static Location<'static>, PhantomData<(I, O, E)>);

/// A parser that can be used wherever you need to implement a parser later.
///
/// This parser is analogous to the [`todo!`] and [`unimplemented!`] macros, but will produce a panic when used to
/// parse input, not immediately when invoked.
///
/// This function is useful when developing your parser, allowing you to prototype and run parts of your parser without
/// committing to implementing the entire thing immediately.
///
/// The output type of this parser is whatever you want it to be: it'll never produce output!
///
/// # Examples
///
/// ```should_panic
/// # use chumsky::prelude::*;
/// let int = just::<_, _, Simple<char>>("0x").ignore_then(todo())
///     .or(just("0b").ignore_then(text::digits(2)))
///     .or(text::int(10));
///
/// // Decimal numbers are parsed
/// assert_eq!(int.parse("12"), Ok("12".to_string()));
/// // Binary numbers are parsed
/// assert_eq!(int.parse("0b00101"), Ok("00101".to_string()));
/// // Parsing hexadecimal numbers results in a panic because the parser is unimplemented
/// int.parse("0xd4");
/// ```
#[track_caller]
pub fn todo<I, O, E>() -> Todo<I, O, E> {
    Todo(Location::caller(), PhantomData)
}

impl<I, O, E> Copy for Todo<I, O, E> {}
impl<I, O, E> Clone for Todo<I, O, E> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

impl<I: Clone, O, E: Error<I>> Parser<I, O> for Todo<I, O, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        _debugger: &mut D,
        _stream: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        todo!(
            "Attempted to use an unimplemented parser. Parser defined at {}",
            self.0
        )
    }

    fn parse_inner_verbose(
        &self,
        d: &mut Verbose,
        s: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(
        &self,
        d: &mut Silent,
        s: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

/// See [`choice`].
#[must_use]
pub struct Choice<T, E>(pub(crate) T, pub(crate) PhantomData<E>);

impl<T: Copy, E> Copy for Choice<T, E> {}
impl<T: Clone, E> Clone for Choice<T, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<I: Clone, O, E: Error<I>, A: Parser<I, O, Error = E>, const N: usize> Parser<I, O>
    for Choice<[A; N], E>
{
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        let Choice(parsers, _) = self;
        let mut alt = None;

        for parser in parsers {
            match stream.try_parse(|stream| {
                #[allow(deprecated)]
                debugger.invoke(parser, stream)
            }) {
                (errors, Ok(out)) => return (errors, Ok(out)),
                (_, Err(a_alt)) => {
                    alt = merge_alts(alt.take(), Some(a_alt));
                }
            };
        }

        (Vec::new(), Err(alt.unwrap()))
    }

    fn parse_inner_verbose(
        &self,
        d: &mut Verbose,
        s: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }

    fn parse_inner_silent(
        &self,
        d: &mut Silent,
        s: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

impl<I: Clone, O, E: Error<I>, A: Parser<I, O, Error = E>> Parser<I, O> for Choice<Vec<A>, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        let Choice(parsers, _) = self;
        let mut alt = None;

        for parser in parsers {
            match stream.try_parse(|stream| {
                #[allow(deprecated)]
                debugger.invoke(parser, stream)
            }) {
                (errors, Ok(out)) => return (errors, Ok(out)),
                (_, Err(a_alt)) => {
                    alt = merge_alts(alt.take(), Some(a_alt));
                }
            };
        }

        (Vec::new(), Err(alt.unwrap()))
    }

    fn parse_inner_verbose(
        &self,
        d: &mut Verbose,
        s: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }

    fn parse_inner_silent(
        &self,
        d: &mut Silent,
        s: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

macro_rules! impl_for_tuple {
    () => {};
    ($head:ident $($X:ident)*) => {
        impl_for_tuple!($($X)*);
        impl_for_tuple!(~ $head $($X)*);
    };
    (~ $($X:ident)*) => {
        #[allow(unused_variables, non_snake_case)]
        impl<I: Clone, O, E: Error<I>, $($X: Parser<I, O, Error = E>),*> Parser<I, O> for Choice<($($X,)*), E> {
            type Error = E;

            fn parse_inner<D: Debugger>(
                &self,
                debugger: &mut D,
                stream: &mut StreamOf<I, Self::Error>,
            ) -> PResult<I, O, Self::Error> {
                let Choice(($($X,)*), _) = self;
                let mut alt = None;
                $(
                    match stream.try_parse(|stream| {
                        #[allow(deprecated)]
                        debugger.invoke($X, stream)
                    }) {
                        (errors, Ok(out)) => return (errors, Ok(out)),
                        (errors, Err(a_alt)) => {
                            alt = merge_alts(alt.take(), Some(a_alt));
                        },
                    };
                )*
                (Vec::new(), Err(alt.unwrap()))
            }

            fn parse_inner_verbose(
                &self,
                d: &mut Verbose,
                s: &mut StreamOf<I, Self::Error>,
            ) -> PResult<I, O, Self::Error> {
                #[allow(deprecated)]
                self.parse_inner(d, s)
            }
            fn parse_inner_silent(
                &self,
                d: &mut Silent,
                s: &mut StreamOf<I, Self::Error>,
            ) -> PResult<I, O, Self::Error> {
                #[allow(deprecated)]
                self.parse_inner(d, s)
            }
        }
    };
}

impl_for_tuple!(A_ B_ C_ D_ E_ F_ G_ H_ I_ J_ K_ L_ M_ N_ O_ P_ Q_ S_ T_ U_ V_ W_ X_ Y_ Z_);

/// Parse using a tuple or array of many parsers, producing the output of the first to successfully parse.
///
/// This primitive has a twofold improvement over a chain of [`Parser::or`] calls:
///
/// - Rust's trait solver seems to resolve the [`Parser`] impl for this type much faster, significantly reducing
///   compilation times.
///
/// - Parsing is likely a little faster in some cases because the resulting parser is 'less careful' about error
///   routing, and doesn't perform the same fine-grained error prioritisation that [`Parser::or`] does.
///
/// These qualities make this parser ideal for lexers.
///
/// The output type of this parser is the output type of the inner parsers.
///
/// # Examples
/// ```
/// # use chumsky::prelude::*;
/// #[derive(Clone, Debug, PartialEq)]
/// enum Token {
///     If,
///     For,
///     While,
///     Fn,
///     Int(u64),
///     Ident(String),
/// }
///
/// let tokens = choice::<_, Simple<char>>((
///     text::keyword("if").to(Token::If),
///     text::keyword("for").to(Token::For),
///     text::keyword("while").to(Token::While),
///     text::keyword("fn").to(Token::Fn),
///     text::int(10).from_str().unwrapped().map(Token::Int),
///     text::ident().map(Token::Ident),
/// ))
///     .padded()
///     .repeated();
///
/// use Token::*;
/// assert_eq!(
///     tokens.parse("if 56 for foo while 42 fn bar"),
///     Ok(vec![If, Int(56), For, Ident("foo".to_string()), While, Int(42), Fn, Ident("bar".to_string())]),
/// );
/// ```
///
/// If you have more than 26 choices, the array-form of choice will work for any length. The downside
/// being that the contained parsers must all be of the same type.
/// ```
/// # use chumsky::prelude::*;
/// #[derive(Clone, Debug, PartialEq)]
/// enum Token {
///     If,
///     For,
///     While,
///     Fn,
///     Def,
/// }
///
/// let tokens = choice::<_, Simple<char>>([
///     text::keyword("if").to(Token::If),
///     text::keyword("for").to(Token::For),
///     text::keyword("while").to(Token::While),
///     text::keyword("fn").to(Token::Fn),
///     text::keyword("def").to(Token::Def),
/// ])
///     .padded()
///     .repeated();
///
/// use Token::*;
/// assert_eq!(
///     tokens.parse("def fn while if for"),
///     Ok(vec![Def, Fn, While, If, For]),
/// );
/// ```
pub fn choice<T, E>(parsers: T) -> Choice<T, E> {
    Choice(parsers, PhantomData)
}
