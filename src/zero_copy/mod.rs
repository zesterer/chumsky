#![allow(missing_docs)]

macro_rules! go_extra {
    ( $O :ty ) => {
        fn go_emit(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<Emit, $O, E> {
            Parser::<I, $O, E, S>::go::<Emit>(self, inp)
        }
        fn go_check(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<Check, $O, E> {
            Parser::<I, $O, E, S>::go::<Check>(self, inp)
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
        primitive::{any, choice, empty, end, group, just, none_of, one_of, take_until, todo},
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

        fn invoke<'a, I, O, E, S, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, I, E, S>,
        ) -> PResult<Self, O, E>
        where
            I: Input + ?Sized,
            E: Error<I>,
            S: 'a,
            P: Parser<'a, I, O, E, S> + ?Sized;
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

        fn invoke<'a, I, O, E, S, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, I, E, S>,
        ) -> PResult<Self, O, E>
        where
            I: Input + ?Sized,
            E: Error<I>,
            S: 'a,
            P: Parser<'a, I, O, E, S> + ?Sized,
        {
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

        fn invoke<'a, I, O, E, S, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, I, E, S>,
        ) -> PResult<Self, O, E>
        where
            I: Input + ?Sized,
            E: Error<I>,
            S: 'a,
            P: Parser<'a, I, O, E, S> + ?Sized,
        {
            parser.go_check(inp)
        }
    }
}

pub trait Parser<'a, I: Input + ?Sized, O, E: Error<I> = (), S: 'a = ()> {
    fn parse(&self, input: &'a I) -> (Option<O>, Vec<E>)
    where
        Self: Sized,
        S: Default,
    {
        self.parse_with_state(input, &mut S::default())
    }

    fn parse_with_state(&self, input: &'a I, state: &mut S) -> (Option<O>, Vec<E>)
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
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E>
    where
        Self: Sized;

    #[doc(hidden)]
    fn go_emit(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<Emit, O, E>;
    #[doc(hidden)]
    fn go_check(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<Check, O, E>;

    fn map_slice<U, F: Fn(&'a I::Slice) -> U>(self, f: F) -> MapSlice<'a, Self, I, O, E, S, F, U>
    where
        Self: Sized,
        I: SliceInput,
        I::Slice: 'a,
    {
        MapSlice {
            parser: self,
            mapper: f,
            phantom: PhantomData,
        }
    }

    fn filter<F: Fn(&O) -> bool>(self, f: F) -> Filter<Self, F>
    where
        Self: Sized,
    {
        Filter {
            parser: self,
            filter: f,
        }
    }

    fn map<U, F: Fn(O) -> U>(self, f: F) -> Map<Self, O, F>
    where
        Self: Sized,
    {
        Map {
            parser: self,
            mapper: f,
            phantom: PhantomData,
        }
    }

    fn map_with_span<U, F: Fn(O, I::Span) -> U>(self, f: F) -> MapWithSpan<Self, O, F>
    where
        Self: Sized,
    {
        MapWithSpan {
            parser: self,
            mapper: f,
            phantom: PhantomData,
        }
    }

    fn map_with_state<U, F: Fn(O, I::Span, &mut S) -> U>(self, f: F) -> MapWithState<Self, O, F>
    where
        Self: Sized,
    {
        MapWithState {
            parser: self,
            mapper: f,
            phantom: PhantomData,
        }
    }

    #[doc(alias = "filter_map")]
    fn try_map<U, F: Fn(O, I::Span) -> Result<U, E>>(self, f: F) -> TryMap<Self, O, F>
    where
        Self: Sized,
    {
        TryMap {
            parser: self,
            mapper: f,
            phantom: PhantomData,
        }
    }

    fn try_map_with_state<U, F: Fn(O, I::Span, &mut S) -> Result<U, E>>(
        self,
        f: F,
    ) -> TryMapWithState<Self, O, F>
    where
        Self: Sized,
    {
        TryMapWithState {
            parser: self,
            mapper: f,
            phantom: PhantomData,
        }
    }

    fn ignored(self) -> Ignored<Self, E, S>
    where
        Self: Sized,
    {
        Ignored {
            parser: self,
            to: (),
            phantom: PhantomData,
        }
    }

    fn to<U: Clone>(self, to: U) -> To<Self, O, U, E, S>
    where
        Self: Sized,
    {
        To {
            parser: self,
            to,
            phantom: PhantomData,
        }
    }

    fn then<U, B: Parser<'a, I, U, E, S>>(self, other: B) -> Then<Self, B, O, U, E, S>
    where
        Self: Sized,
    {
        Then {
            parser_a: self,
            parser_b: other,
            phantom: PhantomData,
        }
    }

    fn ignore_then<U, B: Parser<'a, I, U, E, S>>(self, other: B) -> IgnoreThen<Self, B, O, E, S>
    where
        Self: Sized,
    {
        IgnoreThen {
            parser_a: self,
            parser_b: other,
            phantom: PhantomData,
        }
    }

    fn then_ignore<U, B: Parser<'a, I, U, E, S>>(self, other: B) -> ThenIgnore<Self, B, U, E, S>
    where
        Self: Sized,
    {
        ThenIgnore {
            parser_a: self,
            parser_b: other,
            phantom: PhantomData,
        }
    }

    fn then_with<U, B: Parser<'a, I, U, E, S>, F: Fn(O) -> B>(
        self,
        then: F,
    ) -> ThenWith<Self, B, O, F, I, E, S>
    where
        Self: Sized,
    {
        ThenWith {
            parser: self,
            then,
            phantom: PhantomData,
        }
    }

    /// ```
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    ///
    /// // Lua-style multiline string literal
    /// let string = just::<_, _, Simple<str>, ()>('=')
    ///     .repeated()
    ///     .map_slice(str::len)
    ///     .padded_by(just('['))
    ///     .then_with(|n| {
    ///         let close = just('=').repeated().exactly(n).padded_by(just(']'));
    ///         any()
    ///             .and_is(close.not())
    ///             .repeated()
    ///             .map_slice(|s| s)
    ///             .then_ignore(close)
    ///     });
    ///
    /// assert_eq!(
    ///     string.parse("[[wxyz]]").0,
    ///     Some("wxyz"),
    /// );
    /// assert_eq!(
    ///     string.parse("[==[abcd]=]efgh]===]ijkl]==]").0,
    ///     Some("abcd]=]efgh]===]ijkl"),
    /// );
    /// ```
    fn and_is<U, B>(self, other: B) -> AndIs<Self, B, U>
    where
        Self: Sized,
        B: Parser<'a, I, U, E, S>,
    {
        AndIs {
            parser_a: self,
            parser_b: other,
            phantom: PhantomData,
        }
    }

    fn delimited_by<U, V, B, C>(self, start: B, end: C) -> DelimitedBy<Self, B, C, U, V>
    where
        Self: Sized,
        B: Parser<'a, I, U, E, S>,
        C: Parser<'a, I, V, E, S>,
    {
        DelimitedBy {
            parser: self,
            start,
            end,
            phantom: PhantomData,
        }
    }

    fn padded_by<U, B>(self, padding: B) -> PaddedBy<Self, B, U>
    where
        Self: Sized,
        B: Parser<'a, I, U, E, S>,
    {
        PaddedBy {
            parser: self,
            padding,
            phantom: PhantomData,
        }
    }

    fn or<B>(self, other: B) -> Or<Self, B>
    where
        Self: Sized,
        B: Parser<'a, I, O, E, S>,
    {
        Or {
            parser_a: self,
            parser_b: other,
        }
    }

    fn or_not(self) -> OrNot<Self>
    where
        Self: Sized,
    {
        OrNot { parser: self }
    }

    /// ```
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Tree<'a> {
    ///     Text(&'a str),
    ///     Group(Vec<Self>),
    /// }
    ///
    /// // Arbitrary text, nested in a tree with { ... } delimiters
    /// let tree = recursive::<_, _, Simple<str>, (), _, _>(|tree| {
    ///     let text = any()
    ///         .and_is(one_of("{}").not())
    ///         .repeated()
    ///         .at_least(1)
    ///         .map_slice(Tree::Text);
    ///
    ///     let group = tree
    ///         .repeated()
    ///         .collect()
    ///         .delimited_by(just('{'), just('}'))
    ///         .map(Tree::Group);
    ///
    ///     text.or(group)
    /// });
    ///
    /// assert_eq!(
    ///     tree.parse("{abcd{efg{hijk}lmn{opq}rs}tuvwxyz}").0,
    ///     Some(Tree::Group(vec![
    ///         Tree::Text("abcd"),
    ///         Tree::Group(vec![
    ///             Tree::Text("efg"),
    ///             Tree::Group(vec![
    ///                 Tree::Text("hijk"),
    ///             ]),
    ///             Tree::Text("lmn"),
    ///             Tree::Group(vec![
    ///                 Tree::Text("opq"),
    ///             ]),
    ///             Tree::Text("rs"),
    ///         ]),
    ///         Tree::Text("tuvwxyz"),
    ///     ])),
    /// );
    /// ```
    fn not(self) -> Not<Self, O>
    where
        Self: Sized,
    {
        Not {
            parser: self,
            phantom: PhantomData,
        }
    }

    fn repeated(self) -> Repeated<Self, O, I, (), E, S>
    where
        Self: Sized,
    {
        Repeated {
            parser: self,
            at_least: 0,
            at_most: None,
            phantom: PhantomData,
        }
    }

    fn repeated_exactly<const N: usize>(self) -> RepeatedExactly<Self, O, (), N>
    where
        Self: Sized,
    {
        RepeatedExactly {
            parser: self,
            phantom: PhantomData,
        }
    }

    fn separated_by<U, B>(self, separator: B) -> SeparatedBy<Self, B, O, U, I, (), E, S>
    where
        Self: Sized,
        B: Parser<'a, I, U, E, S>,
    {
        SeparatedBy {
            parser: self,
            separator,
            at_least: 0,
            at_most: None,
            allow_leading: false,
            allow_trailing: false,
            phantom: PhantomData,
        }
    }

    fn separated_by_exactly<U, B, const N: usize>(
        self,
        separator: B,
    ) -> SeparatedByExactly<Self, B, U, (), N>
    where
        Self: Sized,
        B: Parser<'a, I, U, E, S>,
    {
        SeparatedByExactly {
            parser: self,
            separator,
            allow_leading: false,
            allow_trailing: false,
            phantom: PhantomData,
        }
    }

    fn foldr<A, B, F>(self, f: F) -> Foldr<Self, F, A, B, E, S>
    where
        Self: Parser<'a, I, (A, B), E, S> + Sized,
        A: IntoIterator,
        A::IntoIter: DoubleEndedIterator,
        F: Fn(A::Item, B) -> B,
    {
        Foldr {
            parser: self,
            folder: f,
            phantom: PhantomData,
        }
    }

    fn foldl<A, B, F>(self, f: F) -> Foldl<Self, F, A, B, E, S>
    where
        Self: Parser<'a, I, (A, B), E, S> + Sized,
        B: IntoIterator,
        F: Fn(A, B::Item) -> A,
    {
        Foldl {
            parser: self,
            folder: f,
            phantom: PhantomData,
        }
    }

    fn rewind(self) -> Rewind<Self>
    where
        Self: Sized,
    {
        Rewind { parser: self }
    }

    fn padded(self) -> Padded<Self>
    where
        Self: Sized,
        I: Input,
        I::Token: Char,
    {
        Padded { parser: self }
    }

    fn flatten<T, Inner>(self) -> Map<Self, O, fn(O) -> Vec<T>>
    where
        Self: Sized,
        O: IntoIterator<Item = Inner>,
        Inner: IntoIterator<Item = T>,
    {
        self.map(|xs| xs.into_iter().flat_map(|xs| xs.into_iter()).collect())
    }

    fn recover_with<F: Parser<'a, I, O, E, S>>(self, fallback: F) -> RecoverWith<Self, F>
    where
        Self: Sized,
    {
        RecoverWith {
            parser: self,
            fallback,
        }
    }

    fn map_err<F>(self, f: F) -> MapErr<Self, F>
    where
        Self: Sized,
        F: Fn(E) -> E,
    {
        MapErr {
            parser: self,
            mapper: f,
        }
    }

    fn map_err_with_span<F>(self, f: F) -> MapErrWithSpan<Self, F>
    where
        Self: Sized,
        F: Fn(E, I::Span) -> E,
    {
        MapErrWithSpan {
            parser: self,
            mapper: f,
        }
    }

    fn map_err_with_state<F>(self, f: F) -> MapErrWithState<Self, F>
    where
        Self: Sized,
        F: Fn(E, I::Span, &mut S) -> E,
    {
        MapErrWithState {
            parser: self,
            mapper: f,
        }
    }

    // TODO: Finish implementing this once full error recovery is implemented
    /*fn validate<U, F>(self, f: F) -> Validate<Self, F>
    where
    Self: Sized,
    F: Fn(O, I::Span, &mut dyn FnMut(E)) -> U
    {
    Validate {
    parser: self,
    validator: f,
    }
    }*/

    fn collect<C>(self) -> Map<Self, O, fn(O) -> C>
    where
        Self: Sized,
        O: IntoIterator,
        C: FromIterator<<O as IntoIterator>::Item>,
    {
        self.map(|items| C::from_iter(items.into_iter()))
    }

    fn chain<T, U, P>(
        self,
        other: P,
    ) -> Map<Then<Self, P, O, U, E, S>, (O, U), fn((O, U)) -> Vec<T>>
    where
        Self: Sized,
        O: Chain<T>,
        U: Chain<T>,
        P: Parser<'a, I, U, E, S>,
    {
        self.then(other).map(|(a, b)| {
            let mut v = Vec::with_capacity(a.len() + b.len());
            a.append_to(&mut v);
            b.append_to(&mut v);
            v
        })
    }

    fn or_else<F>(self, f: F) -> OrElse<Self, F>
    where
        Self: Sized,
        F: Fn(E) -> Result<O, E>,
    {
        OrElse {
            parser: self,
            or_else: f,
        }
    }

    fn from_str<U>(self) -> Map<Self, O, fn(O) -> Result<U, U::Err>>
    where
        Self: Sized,
        U: FromStr,
        O: AsRef<str>,
    {
        self.map(|o| o.as_ref().parse())
    }

    fn unwrapped<U, E1>(self) -> Map<Self, Result<U, E1>, fn(Result<U, E1>) -> U>
    where
        Self: Sized + Parser<'a, I, Result<U, E1>, E, S>,
        E1: fmt::Debug,
    {
        self.map(|o| o.unwrap())
    }

    fn boxed(self) -> Boxed<'a, I, O, E, S>
    where
        Self: Sized + 'a,
    {
        Boxed {
            inner: Rc::new(self),
        }
    }
}

pub struct Boxed<'a, I: ?Sized, O, E, S = ()> {
    inner: Rc<dyn Parser<'a, I, O, E, S> + 'a>,
}

impl<'a, I: ?Sized, E, O, S> Clone for Boxed<'a, I, O, E, S> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, I, O, E, S> Parser<'a, I, O, E, S> for Boxed<'a, I, O, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
        M::invoke(&*self.inner, inp)
    }

    go_extra!(O);
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

    // fn parser2() -> impl Parser<'static, str, TokenTest> {
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

    fn parser<'a>() -> impl Parser<'a, WithContext<'a, FileId, str>, [(Span, Token<'a>); 6]> {
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

use combinator::MapSlice;

#[test]
fn zero_copy_repetition() {
    use self::prelude::*;

    fn parser<'a>() -> impl Parser<'a, str, Vec<u64>> {
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

#[test]
fn zero_copy_group() {
    use self::prelude::*;

    fn parser<'a>() -> impl Parser<'a, str, (&'a str, u64, char)> {
        group((
            any()
                .filter(|c: &char| c.is_ascii_alphabetic())
                .repeated()
                .at_least(1)
                .map_slice(|s: &str| s)
                .padded(),
            any()
                .filter(|c: &char| c.is_ascii_digit())
                .repeated()
                .at_least(1)
                .map_slice(|s: &str| s.parse::<u64>().unwrap())
                .padded(),
            any().filter(|c: &char| !c.is_whitespace()).padded(),
        ))
    }

    assert_eq!(
        parser().parse("abc 123 ["),
        (Some(("abc", 123, '[')), Vec::new())
    );
    assert_eq!(
        parser().parse("among3d"),
        (Some(("among", 3, 'd')), Vec::new())
    );
    assert_eq!(
        parser().parse("cba321,"),
        (Some(("cba", 321, ',')), Vec::new())
    );

    assert!(!parser().parse("abc 123  ").1.is_empty());
    assert!(!parser().parse("123abc ]").1.is_empty());
    assert!(!parser().parse("and one &").1.is_empty());
}

#[cfg(feature = "regex")]
#[test]
fn regex_parser() {
    use self::prelude::*;
    use self::regex::*;

    fn parser<'a, C: Char>() -> impl Parser<'a, C::Slice, Vec<&'a C::Slice>> {
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

#[test]
fn unicode_str() {
    let input = "🄯🄚🹠🴎🄐🝋🰏🄂🬯🈦g🸵🍩🕔🈳2🬙🨞🅢🭳🎅h🵚🧿🏩🰬k🠡🀔🈆🝹🤟🉗🴟📵🰄🤿🝜🙘🹄5🠻🡉🱖🠓";
    let mut state = ();
    let mut input = InputRef::<_, (), _>::new(input, &mut state);

    while let (_, Some(c)) = input.next() {
        std::hint::black_box(c);
    }
}
