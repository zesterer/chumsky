#![allow(missing_docs)]

macro_rules! go_extra {
    () => {
        fn go_emit(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<Emit, Self::Output, E> {
            Parser::<I, E, S>::go::<Emit>(self, inp)
        }
        fn go_check(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<Check, Self::Output, E> {
            Parser::<I, E, S>::go::<Check>(self, inp)
        }
    };
}

mod blanket;
pub mod chain;
pub mod combinator;
pub mod error;
pub mod input;
pub mod primitive;
pub mod recursive;
#[cfg(feature = "regex")]
pub mod regex;
pub mod span;
pub mod text;

pub mod prelude {
    pub use super::{
        error::{Error as _, Rich, Simple},
        primitive::{any, choice, empty, end, just, none_of, one_of, take_until, todo},
        // recovery::{nested_delimiters, skip_then_retry_until, skip_until},
        recursive::{recursive, Recursive},
        // select,
        span::Span as _,
        text,
        Boxed,
        Parser,
    };
}

use alloc::{
    boxed::Box,
    rc::{Rc, Weak},
    string::String,
    vec::Vec,
};
use core::{
    cell::OnceCell,
    cmp::{Eq, Ordering},
    fmt,
    hash::Hash,
    iter::FromIterator,
    marker::PhantomData,
    ops::{Range, RangeFrom},
    str::FromStr,
    panic::Location,
};
use hashbrown::HashMap;

use self::{
    chain::Chain,
    combinator::*,
    error::Error,
    input::{Input, InputRef, SliceInput, StrInput},
    internal::*,
    span::Span,
    text::*,
};

pub type PResult<M, O, E> = Result<<M as Mode>::Output<O>, Located<E>>;

#[doc(hidden)]
pub struct Located<E> {
    pos: usize,
    err: E,
}

impl<E> Located<E> {
    fn at(pos: usize, err: E) -> Self {
        Self { pos, err }
    }

    fn prioritize(self, other: Self, merge: impl FnOnce(E, E) -> E) -> Self {
        match self.pos.cmp(&other.pos) {
            Ordering::Equal => Self::at(self.pos, merge(self.err, other.err)),
            Ordering::Greater => self,
            Ordering::Less => other,
        }
    }
}

mod internal {
    use super::*;

    pub trait Mode {
        type Output<T>;
        fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T>;
        fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U>;
        fn combine<T, U, V, F: FnOnce(T, U) -> V>(
            x: Self::Output<T>,
            y: Self::Output<U>,
            f: F,
        ) -> Self::Output<V>;
        fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]>;

        fn invoke<'a, I: Input + ?Sized, E: Error<I>, S: 'a, P: Parser<'a, I, E, S> + ?Sized>(
            parser: &P,
            inp: &mut InputRef<'a, '_, I, E, S>,
        ) -> PResult<Self, P::Output, E>;
    }

    pub struct Emit;
    impl Mode for Emit {
        type Output<T> = T;
        fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T> {
            f()
        }
        fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> {
            f(x)
        }
        fn combine<T, U, V, F: FnOnce(T, U) -> V>(
            x: Self::Output<T>,
            y: Self::Output<U>,
            f: F,
        ) -> Self::Output<V> {
            f(x, y)
        }
        fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]> {
            x
        }

        fn invoke<'a, I: Input + ?Sized, E: Error<I>, S: 'a, P: Parser<'a, I, E, S> + ?Sized>(
            parser: &P,
            inp: &mut InputRef<'a, '_, I, E, S>,
        ) -> PResult<Self, P::Output, E> {
            parser.go_emit(inp)
        }
    }

    pub struct Check;
    impl Mode for Check {
        type Output<T> = ();
        fn bind<T, F: FnOnce() -> T>(_: F) -> Self::Output<T> {}
        fn map<T, U, F: FnOnce(T) -> U>(_: Self::Output<T>, _: F) -> Self::Output<U> {}
        fn combine<T, U, V, F: FnOnce(T, U) -> V>(
            _: Self::Output<T>,
            _: Self::Output<U>,
            _: F,
        ) -> Self::Output<V> {
        }
        fn array<T, const N: usize>(_: [Self::Output<T>; N]) -> Self::Output<[T; N]> {}

        fn invoke<'a, I: Input + ?Sized, E: Error<I>, S: 'a, P: Parser<'a, I, E, S> + ?Sized>(
            parser: &P,
            inp: &mut InputRef<'a, '_, I, E, S>,
        ) -> PResult<Self, P::Output, E> {
            parser.go_check(inp)
        }
    }
}

pub trait Parser<'a, I: Input + ?Sized, E: Error<I> = (), S: 'a = ()> {
    type Output;

    fn parse(&self, input: &'a I) -> (Option<Self::Output>, Vec<E>)
    where
        Self: Sized,
        S: Default,
    {
        self.parse_with_state(input, &mut S::default())
    }

    fn parse_with_state(&self, input: &'a I, state: &mut S) -> (Option<Self::Output>, Vec<E>)
    where
        Self: Sized,
    {
        let mut inp = InputRef::new(input, state);
        let res = self.go::<Emit>(&mut inp);
        let mut errs = inp.into_errs();
        let out = match res {
            Ok(out) => Some(out),
            Err(e) => {
                errs.push(e.err);
                None
            }
        };
        (out, errs)
    }

    fn check(&self, input: &'a I) -> Vec<E>
    where
        Self: Sized,
        S: Default,
    {
        let mut state = S::default();
        let mut inp = InputRef::new(input, &mut state);
        let res = self.go::<Check>(&mut inp);
        let mut errs = inp.into_errs();
        if let Err(e) = res {
            errs.push(e.err);
        };
        errs
    }

    #[doc(hidden)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E>
    where
        Self: Sized;

    #[doc(hidden)]
    fn go_emit(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<Emit, Self::Output, E>;
    #[doc(hidden)]
    fn go_check(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<Check, Self::Output, E>;

    #[track_caller]
    fn map_slice<O, F: Fn(&'a I::Slice) -> O>(self, f: F) -> MapSlice<Self, F, E, S>
    where
        Self: Sized,
        I: SliceInput,
        I::Slice: 'a,
    {
        MapSlice {
            parser: self,
            mapper: f,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn filter<F: Fn(&Self::Output) -> bool>(self, f: F) -> Filter<Self, F>
    where
        Self: Sized,
    {
        Filter {
            parser: self,
            filter: f,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn map<O, F: Fn(Self::Output) -> O>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
    {
        Map {
            parser: self,
            mapper: f,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn map_with_span<O, F: Fn(Self::Output, I::Span) -> O>(self, f: F) -> MapWithSpan<Self, F>
    where
        Self: Sized,
    {
        MapWithSpan {
            parser: self,
            mapper: f,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn map_with_state<O, F: Fn(Self::Output, I::Span, &mut S) -> O>(
        self,
        f: F,
    ) -> MapWithState<Self, F>
    where
        Self: Sized,
    {
        MapWithState {
            parser: self,
            mapper: f,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    #[doc(alias = "filter_map")]
    fn try_map<O, F: Fn(Self::Output, I::Span) -> Result<O, E>>(self, f: F) -> TryMap<Self, F>
    where
        Self: Sized,
    {
        TryMap {
            parser: self,
            mapper: f,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn try_map_with_state<O, F: Fn(Self::Output, I::Span, &mut S) -> Result<O, E>>(
        self,
        f: F,
    ) -> TryMapWithState<Self, F>
    where
        Self: Sized,
    {
        TryMapWithState {
            parser: self,
            mapper: f,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn ignored(self) -> Ignored<Self, E, S>
    where
        Self: Sized,
    {
        Ignored {
            parser: self,
            to: (),
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn to<O: Clone>(self, to: O) -> To<Self, O, E, S>
    where
        Self: Sized,
    {
        To {
            parser: self,
            to,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn then<B: Parser<'a, I, E, S>>(self, other: B) -> Then<Self, B, E, S>
    where
        Self: Sized,
    {
        Then {
            parser_a: self,
            parser_b: other,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn ignore_then<B: Parser<'a, I, E, S>>(self, other: B) -> IgnoreThen<Self, B, E, S>
    where
        Self: Sized,
    {
        IgnoreThen {
            parser_a: self,
            parser_b: other,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn then_ignore<B: Parser<'a, I, E, S>>(self, other: B) -> ThenIgnore<Self, B, E, S>
    where
        Self: Sized,
    {
        ThenIgnore {
            parser_a: self,
            parser_b: other,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn then_with<B: Parser<'a, I, E, S>, F: Fn(Self::Output) -> B>(
        self,
        then: F,
    ) -> ThenWith<Self, B, F, I, E, S>
    where
        Self: Sized,
    {
        ThenWith {
            parser: self,
            then,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn delimited_by<B: Parser<'a, I, E, S>, C: Parser<'a, I, E, S>>(
        self,
        start: B,
        end: C,
    ) -> DelimitedBy<Self, B, C>
    where
        Self: Sized,
    {
        DelimitedBy {
            parser: self,
            start,
            end,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn padded_by<B: Parser<'a, I, E, S>>(self, padding: B) -> PaddedBy<Self, B>
    where
        Self: Sized,
    {
        PaddedBy {
            parser: self,
            padding,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn or<B: Parser<'a, I, E, S, Output = Self::Output>>(self, other: B) -> Or<Self, B>
    where
        Self: Sized,
    {
        Or {
            parser_a: self,
            parser_b: other,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn or_not(self) -> OrNot<Self>
    where
        Self: Sized,
    {
        OrNot {
            parser: self,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn repeated(self) -> Repeated<Self, I, (), E, S>
    where
        Self: Sized,
    {
        Repeated {
            parser: self,
            at_least: 0,
            at_most: None,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn repeated_exactly<const N: usize>(self) -> RepeatedExactly<Self, (), N>
    where
        Self: Sized,
    {
        RepeatedExactly {
            parser: self,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn separated_by<B: Parser<'a, I, E, S>>(self, separator: B) -> SeparatedBy<Self, B, I, (), E, S>
    where
        Self: Sized,
    {
        SeparatedBy {
            parser: self,
            separator,
            at_least: 0,
            at_most: None,
            allow_leading: false,
            allow_trailing: false,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn separated_by_exactly<B: Parser<'a, I, E, S>, const N: usize>(
        self,
        separator: B,
    ) -> SeparatedByExactly<Self, B, (), N>
    where
        Self: Sized,
    {
        SeparatedByExactly {
            parser: self,
            separator,
            allow_leading: false,
            allow_trailing: false,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn foldr<A, B, F>(self, f: F) -> Foldr<Self, F, A, B, E, S>
    where
        Self: Parser<'a, I, E, S, Output = (A, B)> + Sized,
        A: IntoIterator,
        A::IntoIter: DoubleEndedIterator,
        F: Fn(A::Item, B) -> B,
    {
        Foldr {
            parser: self,
            folder: f,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn foldl<A, B, F>(self, f: F) -> Foldl<Self, F, A, B, E, S>
    where
        Self: Parser<'a, I, E, S, Output = (A, B)> + Sized,
        B: IntoIterator,
        F: Fn(A, B::Item) -> A,
    {
        Foldl {
            parser: self,
            folder: f,
            phantom: PhantomData,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn rewind(self) -> Rewind<Self>
    where
        Self: Sized,
    {
        Rewind {
            parser: self,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn padded(self) -> Padded<Self>
    where
        Self: Sized,
        I: Input,
        I::Token: Char,
    {
        Padded {
            parser: self,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn flatten<T, Inner>(self) -> Map<Self, fn(Self::Output) -> Vec<T>>
    where
        Self: Sized,
        Self::Output: IntoIterator<Item = Inner>,
        Inner: IntoIterator<Item = T>,
    {
        self.map(|xs| xs.into_iter().flat_map(|xs| xs.into_iter()).collect())
    }

    #[track_caller]
    fn recover_with<F: Parser<'a, I, E, S, Output = Self::Output>>(
        self,
        fallback: F,
    ) -> RecoverWith<Self, F>
    where
        Self: Sized,
    {
        RecoverWith {
            parser: self,
            fallback,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn map_err<F>(self, f: F) -> MapErr<Self, F>
    where
        Self: Sized,
        F: Fn(E) -> E,
    {
        MapErr {
            parser: self,
            mapper: f,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn map_err_with_span<F>(self, f: F) -> MapErrWithSpan<Self, F>
    where
        Self: Sized,
        F: Fn(E, I::Span) -> E,
    {
        MapErrWithSpan {
            parser: self,
            mapper: f,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn map_err_with_state<F>(self, f: F) -> MapErrWithState<Self, F>
    where
        Self: Sized,
        F: Fn(E, I::Span, &mut S) -> E,
    {
        MapErrWithState {
            parser: self,
            mapper: f,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    // TODO: Finish implementing this once full error recovery is implemented
    /*
    #[track_caller]
    fn validate<U, F>(self, f: F) -> Validate<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Output, I::Span, &mut dyn FnMut(E)) -> U
    {
        Validate {
            parser: self,
            validator: f,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }*/

    #[track_caller]
    fn collect<C>(self) -> Map<Self, fn(Self::Output) -> C>
    where
        Self: Sized,
        Self::Output: IntoIterator,
        C: FromIterator<<Self::Output as IntoIterator>::Item>,
    {
        self.map(|items| C::from_iter(items.into_iter()))
    }

    #[track_caller]
    fn chain<T, U, P>(self, other: P) -> Map<Then<Self, P, E, S>, fn((Self::Output, U)) -> Vec<T>>
    where
        Self: Sized,
        Self::Output: Chain<T>,
        U: Chain<T>,
        P: Parser<'a, I, E, S, Output = U>,
    {
        self.then(other).map(|(a, b)| {
            let mut v = Vec::with_capacity(a.len() + b.len());
            a.append_to(&mut v);
            b.append_to(&mut v);
            v
        })
    }

    #[track_caller]
    fn or_else<F>(self, f: F) -> OrElse<Self, F>
    where
        Self: Sized,
        F: Fn(E) -> Result<Self::Output, E>,
    {
        OrElse {
            parser: self,
            or_else: f,
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    #[track_caller]
    fn from_str<U>(self) -> Map<Self, fn(Self::Output) -> Result<U, U::Err>>
    where
        Self: Sized,
        U: FromStr,
        Self::Output: AsRef<str>,
    {
        self.map(|o| o.as_ref().parse())
    }

    #[track_caller]
    fn unwrapped<U, E1>(self) -> Map<Self, fn(Result<U, E1>) -> U>
    where
        Self: Sized + Parser<'a, I, E, S, Output = Result<U, E1>>,
        E1: fmt::Debug,
    {
        self.map(|o| o.unwrap())
    }

    #[track_caller]
    fn boxed(self) -> Boxed<'a, I, Self::Output, E, S>
    where
        Self: Sized + 'a,
    {
        Boxed {
            inner: Rc::new(self),
        }
    }

    #[doc(hidden)]
    #[cfg(debug_assertions)]
    fn details(&self) -> (&str, Location);

    // Returns the minimum and maximum number of inputs consumed by this parser
    #[doc(hidden)]
    #[cfg(debug_assertions)]
    fn fp(&self) -> Range<Option<usize>>;

    #[cfg(debug_assertions)]
    fn find_problems(&self) {
        self.fp();
    }
}

pub struct Boxed<'a, I: ?Sized, O, E, S = ()> {
    inner: Rc<dyn Parser<'a, I, E, S, Output = O> + 'a>,
}

impl<'a, I: ?Sized, E, O, S> Clone for Boxed<'a, I, O, E, S> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, I, E, S, O> Parser<'a, I, E, S> for Boxed<'a, I, O, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        M::invoke(&*self.inner, inp)
    }

    #[cfg(debug_assertions)]
    fn details(&self) -> (&str, Location) { (&*self).details() }

    #[cfg(debug_assertions)]
    fn fp(&self) -> Range<Option<usize>> { (&*self).fp() }

    go_extra!();
}

#[test]
fn zero_copy() {
    use self::input::WithContext;
    use self::prelude::*;

    // #[derive(Clone)]
    // enum TokenTest {
    //     Root,
    //     Branch(Box<Self>),
    // }

    // fn parser2() -> impl Parser<'static, str, Output = TokenTest> {
    //     recursive(|token| {
    //         token
    //             .delimited_by(just('c'), just('c'))
    //             .map(Box::new)
    //             .map(TokenTest::Branch)
    //             .or(just('!').to(TokenTest::Root))
    //     })
    // }

    #[derive(PartialEq, Debug)]
    enum Token<'a> {
        Ident(&'a str),
        String(&'a str),
    }

    type FileId = u32;

    type Span = (FileId, Range<usize>);

    fn parser<'a>() -> impl Parser<'a, WithContext<'a, FileId, str>, Output = [(Span, Token<'a>); 6]>
    {
        let ident = any()
            .filter(|c: &char| c.is_alphanumeric())
            .repeated()
            .at_least(1)
            .map_slice(Token::Ident);

        let string = just('"')
            .then(any().filter(|c: &char| *c != '"').repeated())
            .then(just('"'))
            .map_slice(Token::String);

        ident
            .or(string)
            .map_with_span(|token, span| (span, token))
            .padded()
            .repeated_exactly()
            .collect()
    }

    assert_eq!(
        parser().parse(&WithContext(42, r#"hello "world" these are "test" tokens"#)),
        (
            Some([
                ((42, 0..5), Token::Ident("hello")),
                ((42, 6..13), Token::String("\"world\"")),
                ((42, 14..19), Token::Ident("these")),
                ((42, 20..23), Token::Ident("are")),
                ((42, 24..30), Token::String("\"test\"")),
                ((42, 31..37), Token::Ident("tokens")),
            ]),
            Vec::new()
        ),
    );
}

#[test]
fn zero_copy_repetition() {
    use self::prelude::*;

    fn parser<'a>() -> impl Parser<'a, str, Output = Vec<u64>> {
        any()
            .filter(|c: &char| c.is_ascii_digit())
            .repeated()
            .at_least(1)
            .at_most(3)
            .map_slice(|b: &str| b.parse::<u64>().unwrap())
            .padded()
            .separated_by(just(',').padded())
            .collect()
            .allow_trailing()
            .delimited_by(just('['), just(']'))
    }

    assert_eq!(
        parser().parse("[122 , 23,43,    4, ]"),
        (Some(vec![122, 23, 43, 4]), Vec::new())
    );
    assert_eq!(
        parser().parse("[0, 3, 6, 900,120]"),
        (Some(vec![0, 3, 6, 900, 120]), Vec::new())
    );
    assert_eq!(
        parser().parse("[200,400,50  ,0,0, ]"),
        (Some(vec![200, 400, 50, 0, 0]), Vec::new())
    );

    assert!(!parser().parse("[1234,123,12,1]").1.is_empty());
    assert!(!parser().parse("[,0, 1, 456]").1.is_empty());
    assert!(!parser().parse("[3, 4, 5, 67 89,]").1.is_empty());
}

#[cfg(feature = "regex")]
#[test]
fn regex_parser() {
    use self::prelude::*;
    use self::regex::*;

    fn parser<'a, C: Char>() -> impl Parser<'a, C::Slice, Output = Vec<&'a C::Slice>> {
        regex("[a-zA-Z_][a-zA-Z0-9_]*")
            .padded()
            .repeated()
            .collect()
    }

    assert_eq!(
        parser::<char>().parse("hello world this works"),
        (Some(vec!["hello", "world", "this", "works"]), Vec::new()),
    );

    assert_eq!(
        parser::<u8>().parse(b"hello world this works" as &[_]),
        (
            Some(vec![
                b"hello" as &[_],
                b"world" as &[_],
                b"this" as &[_],
                b"works" as &[_],
            ]),
            Vec::new()
        ),
    );
}

#[cfg(debug_assertions)]
pub fn warning(s: String) {
    eprintln!("[WARNING]\n\n{}", s);
}

#[test]
fn unicode_str() {
    let input = "🄯🄚🹠🴎🄐🝋🰏🄂🬯🈦g🸵🍩🕔🈳2🬙🨞🅢🭳🎅h🵚🧿🏩🰬k🠡🀔🈆🝹🤟🉗🴟📵🰄🤿🝜🙘🹄5🠻🡉🱖🠓";
    let mut state = ();
    let mut input = InputRef::<_, (), _>::new(input, &mut state);

    while let (_, Some(c)) = input.next() {
        std::hint::black_box(c);
    }
}
