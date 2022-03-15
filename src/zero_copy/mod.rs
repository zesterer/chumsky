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
        error::Error as _,
        primitive::{any, choice, empty, end, filter, just, none_of, one_of},
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
    cmp::Eq,
    hash::Hash,
    lazy::OnceCell,
    marker::PhantomData,
    ops::{Range, RangeFrom},
};
use hashbrown::HashMap;

use self::{
    combinator::*,
    error::Error,
    input::{Input, InputRef, SliceInput, StrInput, WithContext},
    span::Span,
    text::*,
    internal::*,
};

pub type PResult<M, O, E> = Result<<M as Mode>::Output<O>, E>;

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

        fn invoke<'a, I: Input + ?Sized, E: Error<I::Token>, S: 'a, P: Parser<'a, I, E, S> + ?Sized>(
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

        fn invoke<'a, I: Input + ?Sized, E: Error<I::Token>, S: 'a, P: Parser<'a, I, E, S> + ?Sized>(
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
        fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> {}
        fn combine<T, U, V, F: FnOnce(T, U) -> V>(
            x: Self::Output<T>,
            y: Self::Output<U>,
            f: F,
        ) -> Self::Output<V> {
        }
        fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]> {}

        fn invoke<'a, I: Input + ?Sized, E: Error<I::Token>, S: 'a, P: Parser<'a, I, E, S> + ?Sized>(
            parser: &P,
            inp: &mut InputRef<'a, '_, I, E, S>,
        ) -> PResult<Self, P::Output, E> {
            parser.go_check(inp)
        }
    }
}

pub trait Parser<'a, I: Input + ?Sized, E: Error<I::Token> = (), S: 'a = ()> {
    type Output;

    fn parse(&self, input: &'a I) -> Result<Self::Output, E>
    where
        Self: Sized,
        S: Default,
    {
        self.go::<Emit>(&mut InputRef::new(input, &mut S::default()))
    }

    fn parse_with_state(&self, input: &'a I, state: &mut S) -> Result<Self::Output, E>
    where
        Self: Sized,
    {
        self.go::<Emit>(&mut InputRef::new(input, state))
    }

    fn check(&self, input: &'a I) -> Result<(), E>
    where
        Self: Sized,
        S: Default,
    {
        self.go::<Check>(&mut InputRef::new(input, &mut S::default()))
    }

    #[doc(hidden)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E>
    where
        Self: Sized;

    #[doc(hidden)]
    fn go_emit(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<Emit, Self::Output, E>;
    #[doc(hidden)]
    fn go_check(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<Check, Self::Output, E>;

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
        }
    }

    fn map<O, F: Fn(Self::Output) -> O>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
    {
        Map {
            parser: self,
            mapper: f,
        }
    }

    fn map_with_span<O, F: Fn(Self::Output, I::Span) -> O>(self, f: F) -> MapWithSpan<Self, F>
    where
        Self: Sized,
    {
        MapWithSpan {
            parser: self,
            mapper: f,
        }
    }

    fn try_map<O, F: Fn(Self::Output, I::Span) -> Result<O, E>>(self, f: F) -> TryMap<Self, F>
    where
        Self: Sized,
    {
        TryMap {
            parser: self,
            mapper: f,
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

    fn to<O: Clone>(self, to: O) -> To<Self, O, E, S>
    where
        Self: Sized,
    {
        To {
            parser: self,
            to,
            phantom: PhantomData,
        }
    }

    fn then<B: Parser<'a, I, E, S>>(self, other: B) -> Then<Self, B, E, S>
    where
        Self: Sized,
    {
        Then {
            parser_a: self,
            parser_b: other,
            phantom: PhantomData,
        }
    }

    fn ignore_then<B: Parser<'a, I, E, S>>(self, other: B) -> IgnoreThen<Self, B, E, S>
    where
        Self: Sized,
    {
        IgnoreThen {
            parser_a: self,
            parser_b: other,
            phantom: PhantomData,
        }
    }

    fn then_ignore<B: Parser<'a, I, E, S>>(self, other: B) -> ThenIgnore<Self, B, E, S>
    where
        Self: Sized,
    {
        ThenIgnore {
            parser_a: self,
            parser_b: other,
            phantom: PhantomData,
        }
    }

    fn then_with<B: Parser<'a, I, E, S>, F: Fn(Self::Output) -> B>(self, then: F) -> ThenWith<Self, B, F, I, E, S>
    where
        Self: Sized,
    {
        ThenWith {
            parser: self,
            then,
            phantom: PhantomData,
        }
    }

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
        }
    }

    fn padded_by<B: Parser<'a, I, E, S>>(self, padding: B) -> PaddedBy<Self, B>
    where
        Self: Sized,
    {
        PaddedBy {
            parser: self,
            padding,
        }
    }

    fn or<B: Parser<'a, I, E, S, Output = Self::Output>>(self, other: B) -> Or<Self, B>
    where
        Self: Sized,
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

    fn repeated(self) -> Repeated<Self, I, (), E, S>
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

    fn repeated_exactly<const N: usize>(self) -> RepeatedExactly<Self, (), N>
    where
        Self: Sized,
    {
        RepeatedExactly {
            parser: self,
            phantom: PhantomData,
        }
    }

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
        }
    }

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
        }
    }

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
        }
    }

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

    fn boxed(self) -> Boxed<'a, I, Self::Output, E, S>
    where
        Self: Sized + 'a,
    {
        Boxed {
            inner: Rc::new(self),
        }
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
    E: Error<I::Token>,
    S: 'a,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        M::invoke(&*self.inner, inp)
    }

    go_extra!();
}

#[test]
fn zero_copy() {
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
        let ident = filter(|c: &char| c.is_alphanumeric())
            .repeated()
            .at_least(1)
            .map_slice(Token::Ident);

        let string = just('"')
            .then(filter(|c: &char| *c != '"').repeated())
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
        Ok([
            ((42, 0..5), Token::Ident("hello")),
            ((42, 6..13), Token::String("\"world\"")),
            ((42, 14..19), Token::Ident("these")),
            ((42, 20..23), Token::Ident("are")),
            ((42, 24..30), Token::String("\"test\"")),
            ((42, 31..37), Token::Ident("tokens")),
        ]),
    );
}

#[test]
fn zero_copy_repetition() {
    use self::prelude::*;

    fn parser<'a>() -> impl Parser<'a, str, Output = Vec<u64>> {
        filter(|c: &char| c.is_ascii_digit())
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
        Ok(vec![122, 23, 43, 4])
    );
    assert_eq!(
        parser().parse("[0, 3, 6, 900,120]"),
        Ok(vec![0, 3, 6, 900, 120])
    );
    assert_eq!(
        parser().parse("[200,400,50  ,0,0, ]"),
        Ok(vec![200, 400, 50, 0, 0])
    );

    assert!(parser().parse("[1234,123,12,1]").is_err());
    assert!(parser().parse("[,0, 1, 456]").is_err());
    assert!(parser().parse("[3, 4, 5, 67 89,]").is_err());
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
        Ok(vec!["hello", "world", "this", "works",]),
    );

    assert_eq!(
        parser::<u8>().parse(b"hello world this works" as &[_]),
        Ok(vec![
            b"hello" as &[_],
            b"world" as &[_],
            b"this" as &[_],
            b"works" as &[_],
        ]),
    );
}

#[test]
fn unicode_str() {
    use self::prelude::*;

    let input = "🄯🄚🹠🴎🄐🝋🰏🄂🬯🈦g🸵🍩🕔🈳2🬙🨞🅢🭳🎅h🵚🧿🏩🰬k🠡🀔🈆🝹🤟🉗🴟📵🰄🤿🝜🙘🹄5🠻🡉🱖🠓";
    let mut state = ();
    let mut input = InputRef::<_, (), _>::new(input, &mut state);

    while let (_, Some(c)) = input.next() {
        std::hint::black_box(c);
    }
}
