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

/// A trait implemented by parsers.
///
/// Parsers take a stream of tokens of type `I` and attempt to parse them into a value of type `O`. In doing so, they
/// may encounter errors. These need not be fatal to the parsing process: syntactic errors can be recovered from and a
/// valid output may still be generated alongside any syntax errors that were encountered along the way. Usually, this
/// output comes in the form of an [Abstract Syntax Tree](https://en.wikipedia.org/wiki/Abstract_syntax_tree) (AST).
///
/// You should not need to implement this trait by hand. If you cannot combine existing combintors (and in particular
/// [`custom`]) to create the combinator you're looking for, please
/// [open an issue](https://github.com/zesterer/chumsky/issues/new)! If you *really* need to implement this trait,
/// please check the documentation in the source: some implementation details have been deliberately hidden.
#[cfg_attr(
    feature = "nightly",
    rustc_on_unimplemented(
        message = "`{Self}` is not a parser from `{I}` to `{O}`",
        label = "This parser is not compatible because it does not implement `Parser<{I}, {O}>`",
        note = "You should check that the output types of your parsers are consistent with combinator you're using",
    )
)]
pub trait Parser<'a, I: Input + ?Sized, O, E: Error<I> = (), S: 'a = ()> {
    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way.
    ///
    /// If `None` is returned (i.e: parsing failed) then there will *always* be at least one item in the error `Vec`.
    /// If you want to include non-default state, use [`Parser::parse_with_state`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[I]`], a [`&str`], or anything implementing [`Stream`] to it.
    fn parse(&self, input: &'a I) -> (Option<O>, Vec<E>)
    where
        Self: Sized,
        S: Default,
    {
        self.parse_with_state(input, &mut S::default())
    }

    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way.
    /// The provided state will be passed on to parsers that expect it, such as [`map_with_state`](Parser::map_with_state).
    ///
    /// If `None` is returned (i.e: parsing failed) then there will *always* be at least one item in the error `Vec`.
    /// If you want to just use a default state value, use [`Parser::parse`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[I]`], a [`&str`], or anything implementing [`Stream`] to it.
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

    /// Parse a stream of tokens, ignoring any output, and returning any errors encountered along the way.
    ///
    /// If parsing failed, then there will *always* be at least one item in the returned `Vec`.
    /// If you want to include non-default state, use [`Parser::check_with_state`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[I]`], a [`&str`], or anything implementing [`Stream`] to it.
    fn check(&self, input: &'a I) -> Vec<E>
    where
        Self: Sized,
        S: Default,
    {
        self.check_with_state(input, &mut S::default())
    }

    /// Parse a stream of tokens, ignoring any output, and returning any errors encountered along the way.
    ///
    /// If parsing failed, then there will *always* be at least one item in the returned `Vec`.
    /// If you want to just use a default state value, use [`Parser::check`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[I]`], a [`&str`], or anything implementing [`Stream`] to it.
    fn check_with_state(&self, input: &'a I, state: &mut S) -> Vec<E>
    where
        Self: Sized,
    {
        let mut inp = InputRef::new(input, state);
        let res = self.go::<Check>(&mut inp);
        let mut errs = inp.into_errs();
        if let Err(e) = res {
            errs.push(e.err);
        };
        errs
    }

    /// Parse a stream with all the bells & whistles. You can use this to implement your own parser combinators. Note
    /// that both the signature and semantic requirements of this function are very likely to change in later versions.
    /// Where possible, prefer more ergonomic combinators provided elsewhere in the crate rather than implementing your
    /// own. For example, [`custom`] provides a flexible, ergonomic way API for process input streams that likely
    /// covers your use-case.
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

    /// Filter the output of this parser, accepting only inputs that match the given predicate.
    ///
    /// The output type of this parser is `I`, the input that was found.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let lowercase = any()
    ///     .filter::<_, _, Simple<char>>(char::is_ascii_lowercase)
    ///     .repeated().at_least(1)
    ///     .then_ignore(end())
    ///     .collect::<String>();
    ///
    /// assert_eq!(lowercase.parse("hello"), Ok("hello".to_string()));
    /// assert!(lowercase.parse("Hello").is_err());
    /// ```
    fn filter<F: Fn(&O) -> bool>(self, f: F) -> Filter<Self, F>
    where
        Self: Sized,
    {
        Filter {
            parser: self,
            filter: f,
        }
    }

    /// Map the output of this parser to another value.
    ///
    /// The output type of this parser is `U`, the same as the function's output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// #[derive(Debug, PartialEq)]
    /// enum Token { Word(String), Num(u64) }
    ///
    /// let word = any()
    ///     .filter::<_, _, Simple<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated().at_least(1)
    ///     .collect::<String>()
    ///     .map(Token::Word);
    ///
    /// let num = any()
    ///     .filter::<_, _, Simple<char>>(|c: &char| c.is_ascii_digit())
    ///     .repeated().at_least(1)
    ///     .collect::<String>()
    ///     .map(|s| Token::Num(s.parse().unwrap()));
    ///
    /// let token = word.or(num);
    ///
    /// assert_eq!(token.parse("test"), Ok(Token::Word("test".to_string())));
    /// assert_eq!(token.parse("42"), Ok(Token::Num(42)));
    /// ```
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

    /// Map the output of this parser to another value, making use of the pattern's span when doing so.
    ///
    /// This is very useful when generating an AST that attaches a span to each AST node.
    ///
    /// The output type of this parser is `U`, the same as the function's output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// use std::ops::Range;
    ///
    /// // It's common for AST nodes to use a wrapper type that allows attaching span information to them
    /// #[derive(Debug, PartialEq)]
    /// pub struct Spanned<T>(T, Range<usize>);
    ///
    /// let ident = text::ident::<_, Simple<char>>()
    ///     .map_with_span(|ident, span| Spanned(ident, span))
    ///     .padded();
    ///
    /// assert_eq!(ident.parse("hello"), Ok(Spanned("hello".to_string(), 0..5)));
    /// assert_eq!(ident.parse("       hello   "), Ok(Spanned("hello".to_string(), 7..12)));
    /// ```
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

    /// Map the output of this parser to another value, making use of the parser's state when doing so.
    ///
    /// This is very useful for parsing non context-free grammars.
    ///
    /// The output type of this parser is `U`, the same as the function's output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// use std::ops::Range;
    ///
    /// // It's common for AST nodes to use a wrapper type that allows attaching span information to them
    /// #[derive(Debug, PartialEq)]
    /// pub struct Spanned<T>(T, Range<usize>);
    ///
    /// let ident = text::ident::<_, Simple<char>>()
    ///     .map_with_span(|ident, span| Spanned(ident, span))
    ///     .padded();
    ///
    /// assert_eq!(ident.parse("hello"), Ok(Spanned("hello".to_string(), 0..5)));
    /// assert_eq!(ident.parse("       hello   "), Ok(Spanned("hello".to_string(), 7..12)));
    /// ```
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

    /// After a successful parse, apply a fallible function to the output. If the function produces an error, treat it
    /// as a parsing error.
    ///
    /// If you wish parsing of this pattern to continue when an error is generated instead of halting, consider using
    /// [`Parser::validate`] instead.
    ///
    /// The output type of this parser is `U`, the [`Ok`] return value of the function.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let byte = text::int::<_, Simple<char>>(10)
    ///     .try_map(|s, span| s
    ///         .parse::<u8>()
    ///         .map_err(|e| Simple::custom(span, format!("{}", e))));
    ///
    /// assert!(byte.parse("255").is_ok());
    /// assert!(byte.parse("256").is_err()); // Out of range
    /// ```
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

    /// After a successful parse, apply a fallible function to the output, making use of the parser's state when
    /// doing so. If the function produces an error, treat it as a parsing error.
    ///
    /// If you wish parsing of this pattern to continue when an error is generated instead of halting, consider using
    /// [`Parser::validate`] instead.
    ///
    /// The output type of this parser is `U`, the [`Ok`] return value of the function.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let byte = text::int::<_, Simple<char>>(10)
    ///     .try_map(|s, span| s
    ///         .parse::<u8>()
    ///         .map_err(|e| Simple::custom(span, format!("{}", e))));
    ///
    /// assert!(byte.parse("255").is_ok());
    /// assert!(byte.parse("256").is_err()); // Out of range
    /// ```
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

    /// Ignore the output of this parser, yielding `()` as an output instead.
    ///
    /// This can be used to reduce the cost of parsing by avoiding unnecessary allocations (most collections containing
    /// [ZSTs](https://doc.rust-lang.org/nomicon/exotic-sizes.html#zero-sized-types-zsts)
    /// [do not allocate](https://doc.rust-lang.org/std/vec/struct.Vec.html#guarantees)). For example, it's common to
    /// want to ignore whitespace in many grammars (see [`text::whitespace`]).
    ///
    /// The output type of this parser is `()`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// // A parser that parses any number of whitespace characters without allocating
    /// let whitespace = filter::<_, _, Cheap<char>>(|c: &char| c.is_whitespace())
    ///     .ignored()
    ///     .repeated();
    ///
    /// assert_eq!(whitespace.parse("    "), Ok(vec![(); 4]));
    /// assert_eq!(whitespace.parse("  hello"), Ok(vec![(); 2]));
    /// ```
    fn ignored(self) -> Ignored<Self, O>
    where
        Self: Sized,
    {
        Ignored {
            parser: self,
            phantom: PhantomData
        }
    }

    /// Transform all outputs of this parser to a pretermined value.
    ///
    /// The output type of this parser is `U`, the type of the predetermined value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// #[derive(Clone, Debug, PartialEq)]
    /// enum Op { Add, Sub, Mul, Div }
    ///
    /// let op = just::<_, _, Cheap<char>>('+').to(Op::Add)
    ///     .or(just('-').to(Op::Sub))
    ///     .or(just('*').to(Op::Mul))
    ///     .or(just('/').to(Op::Div));
    ///
    /// assert_eq!(op.parse("+"), Ok(Op::Add));
    /// assert_eq!(op.parse("/"), Ok(Op::Div));
    /// ```
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

    /// Parse one thing and then another thing, yielding a tuple of the two outputs.
    ///
    /// The output type of this parser is `(O, U)`, a combination of the outputs of both parsers.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let word = filter::<_, _, Cheap<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated().at_least(1)
    ///     .collect::<String>();
    /// let two_words = word.then_ignore(just(' ')).then(word);
    ///
    /// assert_eq!(two_words.parse("dog cat"), Ok(("dog".to_string(), "cat".to_string())));
    /// assert!(two_words.parse("hedgehog").is_err());
    /// ```
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

    /// Parse one thing and then another thing, yielding only the output of the latter.
    ///
    /// The output type of this parser is `U`, the same as the second parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let zeroes = filter::<_, _, Cheap<char>>(|c: &char| *c == '0').ignored().repeated();
    /// let digits = filter(|c: &char| c.is_ascii_digit()).repeated();
    /// let integer = zeroes
    ///     .ignore_then(digits)
    ///     .collect::<String>()
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// assert_eq!(integer.parse("00064"), Ok(64));
    /// assert_eq!(integer.parse("32"), Ok(32));
    /// ```
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

    /// Parse one thing and then another thing, yielding only the output of the former.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let word = filter::<_, _, Cheap<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated().at_least(1)
    ///     .collect::<String>();
    ///
    /// let punctuated = word
    ///     .then_ignore(just('!').or(just('?')).or_not());
    ///
    /// let sentence = punctuated
    ///     .padded() // Allow for whitespace gaps
    ///     .repeated();
    ///
    /// assert_eq!(
    ///     sentence.parse("hello! how are you?"),
    ///     Ok(vec![
    ///         "hello".to_string(),
    ///         "how".to_string(),
    ///         "are".to_string(),
    ///         "you".to_string(),
    ///     ]),
    /// );
    /// ```
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

    /// Parse one thing and then another thing, creating the second parser from the result of
    /// the first. If you only have a couple cases to handle, prefer [`Parser::or`].
    ///
    /// The output of this parser is `U`, the result of the second parser
    ///
    /// Error recovery for this parser may be sub-optimal, as if the first parser succeeds on
    /// recovery then the second produces an error, the primary error will point to the location in
    /// the second parser which failed, ignoring that the first parser may be the root cause. There
    /// may be other pathological errors cases as well.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// // A parser that parses a single letter and then its successor
    /// let successive_letters = one_of::<_, _, Cheap<u8>>((b'a'..=b'z').collect::<Vec<u8>>())
    ///     .then_with(|letter: u8| just(letter + 1));
    ///
    /// assert_eq!(successive_letters.parse(*b"ab"), Ok(b'b')); // 'b' follows 'a'
    /// assert!(successive_letters.parse(*b"ac").is_err()); // 'c' does not follow 'a'
    /// ```
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

    /// Parse the pattern surrounded by the given delimiters.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// // A LISP-style S-expression
    /// #[derive(Debug, PartialEq)]
    /// enum SExpr {
    ///     Ident(String),
    ///     Num(u64),
    ///     List(Vec<SExpr>),
    /// }
    ///
    /// let ident = filter::<_, _, Cheap<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated().at_least(1)
    ///     .collect::<String>();
    ///
    /// let num = text::int(10)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let s_expr = recursive(|s_expr| s_expr
    ///     .padded()
    ///     .repeated()
    ///     .map(SExpr::List)
    ///     .delimited_by(just('('), just(')'))
    ///     .or(ident.map(SExpr::Ident))
    ///     .or(num.map(SExpr::Num)));
    ///
    /// // A valid input
    /// assert_eq!(
    ///     s_expr.parse_recovery("(add (mul 42 3) 15)"),
    ///     (
    ///         Some(SExpr::List(vec![
    ///             SExpr::Ident("add".to_string()),
    ///             SExpr::List(vec![
    ///                 SExpr::Ident("mul".to_string()),
    ///                 SExpr::Num(42),
    ///                 SExpr::Num(3),
    ///             ]),
    ///             SExpr::Num(15),
    ///         ])),
    ///         Vec::new(), // No errors!
    ///     ),
    /// );
    /// ```
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

    /// Parse a pattern, but with an instance of another pattern on either end, yielding the output of the inner.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let ident = text::ident::<_, Simple<char>>()
    ///     .padded_by(just('!'));
    ///
    /// assert_eq!(ident.parse("!hello!"), Ok("hello".to_string()));
    /// assert!(ident.parse("hello!").is_err());
    /// assert!(ident.parse("!hello").is_err());
    /// assert!(ident.parse("hello").is_err());
    /// ```
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

    /// Parse one thing or, on failure, another thing.
    ///
    /// The output of both parsers must be of the same type, because either output can be produced.
    ///
    /// If both parser succeed, the output of the first parser is guaranteed to be prioritised over the output of the
    /// second.
    ///
    /// If both parsers produce errors, the combinator will attempt to select from or combine the errors to produce an
    /// error that is most likely to be useful to a human attempting to understand the problem. The exact algorithm
    /// used is left unspecified, and is not part of the crate's semver guarantees, although regressions in error
    /// quality should be reported in the issue tracker of the main repository.
    ///
    /// Please note that long chains of [`Parser::or`] combinators have been known to result in poor compilation times.
    /// If you feel you are experiencing this, consider using [`choice`] instead.
    ///
    /// The output type of this parser is `O`, the output of both parsers.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let op = just::<_, _, Cheap<char>>('+')
    ///     .or(just('-'))
    ///     .or(just('*'))
    ///     .or(just('/'));
    ///
    /// assert_eq!(op.parse("+"), Ok('+'));
    /// assert_eq!(op.parse("/"), Ok('/'));
    /// assert!(op.parse("!").is_err());
    /// ```
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

    /// Attempt to parse something, but only if it exists.
    ///
    /// If parsing of the pattern is successful, the output is `Some(_)`. Otherwise, the output is `None`.
    ///
    /// The output type of this parser is `Option<O>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let word = filter::<_, _, Cheap<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated().at_least(1)
    ///     .collect::<String>();
    ///
    /// let word_or_question = word
    ///     .then(just('?').or_not());
    ///
    /// assert_eq!(word_or_question.parse("hello?"), Ok(("hello".to_string(), Some('?'))));
    /// assert_eq!(word_or_question.parse("wednesday"), Ok(("wednesday".to_string(), None)));
    /// ```
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

    /// Parse a pattern any number of times (including zero times).
    ///
    /// Input is eagerly parsed. Be aware that the parser will accept no occurences of the pattern too. Consider using
    /// [`Repeated::at_least`] instead if it better suits your use-case.
    ///
    /// The output type of this parser can be any [`Container`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let num = filter::<_, _, Cheap<char>>(|c: &char| c.is_ascii_digit())
    ///     .repeated().at_least(1)
    ///     .collect::<String>()
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let sum = num.then(just('+').ignore_then(num).repeated())
    ///     .foldl(|a, b| a + b);
    ///
    /// assert_eq!(sum.parse("2+13+4+0+5"), Ok(24));
    /// ```
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

    /// Parse a pattern a specific number of times.
    ///
    /// Input is eagerly parsed. Consider using [`Repeated::repeated`] if a non-constant number of values are expected.
    ///
    /// The output type of this parser can be any [`ContainerExactly`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let num = filter::<_, _, Cheap<char>>(|c: &char| c.is_ascii_digit())
    ///     .repeated().at_least(1)
    ///     .collect::<String>()
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let sum = num.then(just('+').ignore_then(num).repeated())
    ///     .foldl(|a, b| a + b);
    ///
    /// assert_eq!(sum.parse("2+13+4+0+5"), Ok(24));
    /// ```
    fn repeated_exactly<const N: usize>(self) -> RepeatedExactly<Self, O, (), N>
    where
        Self: Sized,
    {
        RepeatedExactly {
            parser: self,
            phantom: PhantomData,
        }
    }

    /// Parse a pattern, separated by another, any number of times.
    ///
    /// You can use [`SeparatedBy::allow_leading`] or [`SeparatedBy::allow_trailing`] to allow leading or trailing
    /// separators.
    ///
    /// The output type of this parser can be any [`Container`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let shopping = text::ident::<_, Simple<char>>()
    ///     .padded()
    ///     .separated_by(just(','));
    ///
    /// assert_eq!(shopping.parse("eggs"), Ok(vec!["eggs".to_string()]));
    /// assert_eq!(shopping.parse("eggs, flour, milk"), Ok(vec!["eggs".to_string(), "flour".to_string(), "milk".to_string()]));
    /// ```
    ///
    /// See [`SeparatedBy::allow_leading`] and [`SeparatedBy::allow_trailing`] for more examples.
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

    /// Parse a pattern, separated by another, a specific number of times.
    ///
    /// You can use [`SeparatedBy::allow_leading`] or [`SeparatedBy::allow_trailing`] to allow leading or trailing
    /// separators.
    ///
    /// The output type of this parser can be any [`ContainerExactly`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let shopping = text::ident::<_, Simple<char>>()
    ///     .padded()
    ///     .separated_by(just(','));
    ///
    /// assert_eq!(shopping.parse("eggs"), Ok(vec!["eggs".to_string()]));
    /// assert_eq!(shopping.parse("eggs, flour, milk"), Ok(vec!["eggs".to_string(), "flour".to_string(), "milk".to_string()]));
    /// ```
    ///
    /// See [`SeparatedBy::allow_leading`] and [`SeparatedBy::allow_trailing`] for more examples.
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

    /// Right-fold the output of the parser into a single value.
    ///
    /// The output of the original parser must be of type `(impl IntoIterator<Item = A>, B)`. Because right-folds work
    /// backwards, the iterator must implement [`DoubleEndedIterator`] so that it can be reversed.
    ///
    /// The output type of this parser is `B`, the right-hand component of the original parser's output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let int = text::int::<char, Cheap<char>>(10)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let signed = just('+').to(1)
    ///     .or(just('-').to(-1))
    ///     .repeated()
    ///     .then(int)
    ///     .foldr(|a, b| a * b);
    ///
    /// assert_eq!(signed.parse("3"), Ok(3));
    /// assert_eq!(signed.parse("-17"), Ok(-17));
    /// assert_eq!(signed.parse("--+-+-5"), Ok(5));
    /// ```
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

    /// Left-fold the output of the parser into a single value.
    ///
    /// The output of the original parser must be of type `(A, impl IntoIterator<Item = B>)`.
    ///
    /// The output type of this parser is `A`, the left-hand component of the original parser's output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let int = text::int::<char, Cheap<char>>(10)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let sum = int
    ///     .then(just('+').ignore_then(int).repeated())
    ///     .foldl(|a, b| a + b);
    ///
    /// assert_eq!(sum.parse("1+12+3+9"), Ok(25));
    /// assert_eq!(sum.parse("6"), Ok(6));
    /// ```
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

    /// Parse a pattern. Afterwards, the input stream will be rewound to its original state, as if parsing had not
    /// occurred.
    ///
    /// This combinator is useful for cases in which you wish to avoid a parser accidentally consuming too much input,
    /// causing later parsers to fail as a result. A typical use-case of this is that you want to parse something that
    /// is not followed by something else.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let just_numbers = text::digits::<_, Simple<char>>(10)
    ///     .padded()
    ///     .then_ignore(none_of("+-*/").rewind())
    ///     .separated_by(just(','));
    /// // 3 is not parsed because it's followed by '+'.
    /// assert_eq!(just_numbers.parse("1, 2, 3 + 4"), Ok(vec!["1".to_string(), "2".to_string()]));
    /// ```
    fn rewind(self) -> Rewind<Self>
    where
        Self: Sized,
    {
        Rewind { parser: self }
    }

    /// Parse a pattern, ignoring any amount of whitespace both before and after the pattern.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let ident = text::ident::<_, Simple<char>>().padded();
    ///
    /// // A pattern with no whitespace surrounding it is accepted
    /// assert_eq!(ident.parse("hello"), Ok("hello".to_string()));
    /// // A pattern with arbitrary whitespace surrounding it is also accepted
    /// assert_eq!(ident.parse(" \t \n  \t   world  \t  "), Ok("world".to_string()));
    /// ```
    fn padded(self) -> Padded<Self>
    where
        Self: Sized,
        I: Input,
        I::Token: Char,
    {
        Padded { parser: self }
    }

    /// Flatten a nested collection.
    ///
    /// This use-cases of this method are broadly similar to those of [`Iterator::flatten`].
    ///
    /// The output type of this parser is `Vec<T>`, where the original parser output was
    /// `impl IntoIterator<Item = impl IntoIterator<Item = T>>`.
    fn flatten<T, Inner>(self) -> Map<Self, O, fn(O) -> Vec<T>>
    where
        Self: Sized,
        O: IntoIterator<Item = Inner>,
        Inner: IntoIterator<Item = T>,
    {
        self.map(|xs| xs.into_iter().flat_map(|xs| xs.into_iter()).collect())
    }

    /// Apply a fallback recovery strategy to this parser should it fail.
    ///
    /// There is no silver bullet for error recovery, so this function allows you to specify one of several different
    /// strategies at the location of your choice. Prefer an error recovery strategy that more precisely mirrors valid
    /// syntax where possible to make error recovery more reliable.
    ///
    /// Because chumsky is a [PEG](https://en.m.wikipedia.org/wiki/Parsing_expression_grammar) parser, which always
    /// take the first successful parsing route through a grammar, recovering from an error may cause the parser to
    /// erroneously miss alternative valid routes through the grammar that do not generate recoverable errors. If you
    /// run into cases where valid syntax fails to parse without errors, this might be happening: consider removing
    /// error recovery or switching to a more specific error recovery strategy.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// #[derive(Debug, PartialEq)]
    /// enum Expr {
    ///     Error,
    ///     Int(String),
    ///     List(Vec<Expr>),
    /// }
    ///
    /// let expr = recursive::<_, _, _, _, Simple<char>>(|expr| expr
    ///     .separated_by(just(','))
    ///     .delimited_by(just('['), just(']'))
    ///     .map(Expr::List)
    ///     // If parsing a list expression fails, recover at the next delimiter, generating an error AST node
    ///     .recover_with(nested_delimiters('[', ']', [], |_| Expr::Error))
    ///     .or(text::int(10).map(Expr::Int))
    ///     .padded());
    ///
    /// assert!(expr.parse("five").is_err()); // Text is not a valid expression in this language...
    /// assert!(expr.parse("[1, 2, 3]").is_ok()); // ...but lists and numbers are!
    ///
    /// // This input has two syntax errors...
    /// let (ast, errors) = expr.parse_recovery("[[1, two], [3, four]]");
    /// // ...and error recovery allows us to catch both of them!
    /// assert_eq!(errors.len(), 2);
    /// // Additionally, the AST we get back still has useful information.
    /// assert_eq!(ast, Some(Expr::List(vec![Expr::Error, Expr::Error])));
    /// ```
    fn recover_with<F: Parser<'a, I, O, E, S>>(self, fallback: F) -> RecoverWith<Self, F>
    where
        Self: Sized,
    {
        RecoverWith {
            parser: self,
            fallback,
        }
    }

    /// Map the primary error of this parser to another value.
    ///
    /// This function is most useful when using a custom error type, allowing you to augment errors according to
    /// context.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    // TODO: Map E -> D, not E -> E
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

    /// Map the primary error of this parser to another value, making use of the span from the start of the attempted
    /// to the point at which the error was encountered.
    ///
    /// This function is useful for augmenting errors to allow them to display the span of the initial part of a
    /// pattern, for example to add a "while parsing" clause to your error messages.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    // TODO: Map E -> D, not E -> E
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

    /// Map the primary error of this parser to another value, making use of the parser state.
    ///
    /// This function is useful for augmenting errors to allow them to include context in non context-free
    /// languages, or provide contextual notes on possible causes.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    // TODO: Map E -> D, not E -> E
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

    /// Collect the output of this parser into a type implementing [`FromIterator`].
    ///
    /// This is commonly useful for collecting [`Vec<char>`] outputs into [`String`]s, or [`(T, U)`] into a
    /// [`HashMap`] and is analagous to [`Iterator::collect`].
    ///
    /// The output type of this parser is `C`, the type being collected into.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let word = filter::<_, _, Cheap<char>>(|c: &char| c.is_alphabetic()) // This parser produces an output of `char`
    ///     .repeated() // This parser produces an output of `Vec<char>`
    ///     .collect::<String>(); // But `Vec<char>` is less useful than `String`, so convert to the latter
    ///
    /// assert_eq!(word.parse("hello"), Ok("hello".to_string()));
    /// ```
    // TODO: Make `Parser::repeated` generic over an `impl FromIterator` to reduce required allocations
    fn collect<C>(self) -> Map<Self, O, fn(O) -> C>
    where
        Self: Sized,
        O: IntoIterator,
        C: FromIterator<<O as IntoIterator>::Item>,
    {
        self.map(|items| C::from_iter(items.into_iter()))
    }

    /// Parse one thing and then another thing, attempting to chain the two outputs into a [`Vec`].
    ///
    /// The output type of this parser is `Vec<T>`, composed of the elements of the outputs of both parsers.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let int = just('-').or_not()
    ///     .chain(filter::<_, _, Cheap<char>>(|c: &char| c.is_ascii_digit() && *c != '0')
    ///         .chain(filter::<_, _, Cheap<char>>(|c: &char| c.is_ascii_digit()).repeated()))
    ///     .or(just('0').map(|c| vec![c]))
    ///     .then_ignore(end())
    ///     .collect::<String>()
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// assert_eq!(int.parse("0"), Ok(0));
    /// assert_eq!(int.parse("415"), Ok(415));
    /// assert_eq!(int.parse("-50"), Ok(-50));
    /// assert!(int.parse("-0").is_err());
    /// assert!(int.parse("05").is_err());
    /// ```
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

    /// Map the primary error of this parser to a result. If the result is [`Ok`], the parser succeeds with that value.
    ///
    /// Note that even if the function returns an [`Ok`], the input stream will still be 'stuck' at the input following
    /// the input that triggered the error. You'll need to follow uses of this combinator with a parser that resets
    /// the input stream to a known-good state (for example, [`take_until`]).
    ///
    /// The output type of this parser is `U`, the [`Ok`] type of the result.
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

    /// Attempt to convert the output of this parser into something else using Rust's [`FromStr`] trait.
    ///
    /// This is most useful when wanting to convert literal values into their corresponding Rust type, such as when
    /// parsing integers.
    ///
    /// The output type of this parser is `Result<U, U::Err>`, the result of attempting to parse the output, `O`, into
    /// the value `U`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let uint64 = text::int::<_, Simple<char>>(10)
    ///     .from_str::<u64>()
    ///     .unwrapped();
    ///
    /// assert_eq!(uint64.parse("7"), Ok(7));
    /// assert_eq!(uint64.parse("42"), Ok(42));
    /// ```
    #[allow(clippy::wrong_self_convention)]
    fn from_str<U>(self) -> Map<Self, O, fn(O) -> Result<U, U::Err>>
    where
        Self: Sized,
        U: FromStr,
        O: AsRef<str>,
    {
        self.map(|o| o.as_ref().parse())
    }

    /// For parsers that produce a [`Result`] as their output, unwrap the result (panicking if an [`Err`] is
    /// encountered).
    ///
    /// In general, this method should be avoided except in cases where all possible that the parser might produce can
    /// by parsed using [`FromStr`] without producing an error.
    ///
    /// This combinator is not named `unwrap` to avoid confusion: it unwraps *during parsing*, not immediately.
    ///
    /// The output type of this parser is `U`, the [`Ok`] value of the [`Result`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let boolean = just::<_, _, Simple<char>>("true")
    ///     .or(just("false"))
    ///     .from_str::<bool>()
    ///     .unwrapped(); // Cannot panic: the only possible outputs generated by the parser are "true" or "false"
    ///
    /// assert_eq!(boolean.parse("true"), Ok(true));
    /// assert_eq!(boolean.parse("false"), Ok(false));
    /// // Does not panic, because the original parser only accepts "true" or "false"
    /// assert!(boolean.parse("42").is_err());
    /// ```
    fn unwrapped<U, E1>(self) -> Map<Self, Result<U, E1>, fn(Result<U, E1>) -> U>
    where
        Self: Sized + Parser<'a, I, Result<U, E1>, E, S>,
        E1: fmt::Debug,
    {
        self.map(|o| o.unwrap())
    }

    /// Box the parser, yielding a parser that performs parsing through dynamic dispatch.
    ///
    /// Boxing a parser might be useful for:
    ///
    /// - Dynamically building up parsers at run-time
    ///
    /// - Improving compilation times (Rust can struggle to compile code containing very long types)
    ///
    /// - Passing a parser over an FFI boundary
    ///
    /// - Getting around compiler implementation problems with long types such as
    ///   [this](https://github.com/rust-lang/rust/issues/54540).
    ///
    /// - Places where you need to name the type of a parser
    ///
    /// Boxing a parser is broadly equivalent to boxing other combinators via dynamic dispatch, such as [`Iterator`].
    ///
    /// The output type of this parser is `O`, the same as the original parser.
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
