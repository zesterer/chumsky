//! A zero-copy implementation of [`Parser`](super::Parser)
//!
//! This will likely be moving to the crate root at some point and entirely replacing the current
//! parser implementation.

macro_rules! go_extra {
    ( $Out :ty ) => {
        fn go_emit(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<Emit, $Out, Err> {
            Parser::<In, $Out, Err, State, Ctx>::go::<Emit>(self, inp)
        }
        fn go_check(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<Check, $Out, Err> {
            Parser::<In, $Out, Err, State, Ctx>::go::<Check>(self, inp)
        }
        fn go_cfg_emit(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>, cfg: Self::Config) -> PResult<Emit, $Out, Err> {
            Parser::<In, $Out, Err, State, Ctx>::go_cfg::<Emit>(self, inp, cfg)
        }
        fn go_cfg_check(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>, cfg: Self::Config) -> PResult<Check, $Out, Err> {
            Parser::<In, $Out, Err, State, Ctx>::go_cfg::<Check>(self, inp, cfg)
        }
    };
}

mod blanket;
pub mod chain;
pub mod combinator;
pub mod container;
pub mod error;
pub mod input;
pub mod primitive;
pub mod recursive;
#[cfg(feature = "regex")]
pub mod regex;
pub mod span;
pub mod text;

/// Commonly used functions, traits and types.
///
/// *Listen, three eyes,” he said, “don’t you try to outweird me, I get stranger things than you free with my breakfast
/// cereal.”*
pub mod prelude {
    pub use super::{
        error::{Error as _, EmptyErr, Rich, Simple},
        primitive::{any, choice, empty, end, group, just, none_of, one_of, take_until, todo},
        // recovery::{nested_delimiters, skip_then_retry_until, skip_until},
        recursive::{recursive, Recursive},
        // select,
        span::{Span as _, SimpleSpan},
        text,
        Boxed,
        Parser,
        ParseResult,
    };
}

use alloc::{
    boxed::Box,
    rc::{Rc, Weak},
    string::String,
    vec::Vec,
    vec,
};
use core::{
    borrow::Borrow,
    cmp::{Eq, Ordering},
    fmt,
    hash::Hash,
    iter::FromIterator,
    marker::PhantomData,
    ops::{Range, RangeFrom},
    str::FromStr,
    mem::MaybeUninit,
};
use hashbrown::HashMap;

use self::{
    chain::Chain,
    combinator::*,
    container::*,
    error::{Error, EmptyErr},
    input::{Input, InputRef, SliceInput, StrInput},
    internal::*,
    span::{Span, SimpleSpan},
    text::*,
};

// TODO: Remove this when MaybeUninit transforms to/from arrays stabilize in any form
trait MaybeUninitExt<T>: Sized {
    /// Identical to the unstable [`MaybeUninit::uninit_array`]
    fn uninit_array<const N: usize>() -> [Self; N];

    /// Identical to the unstable [`MaybeUninit::array_assume_init`]
    unsafe fn array_assume_init<const N: usize>(uninit: [Self; N]) -> [T; N];
}

impl<T> MaybeUninitExt<T> for MaybeUninit<T> {
    fn uninit_array<const N: usize>() -> [Self; N] {
        // SAFETY: Output type is entirely uninhabited - IE, it's made up entirely of `MaybeUninit`
        unsafe { MaybeUninit::uninit().assume_init() }
    }

    unsafe fn array_assume_init<const N: usize>(uninit: [Self; N]) -> [T; N] {
        let out = (&uninit as *const [Self; N] as *const [T; N]).read();
        core::mem::forget(uninit);
        out
    }
}

/// The result of calling [`Parser::go`]
pub type PResult<M, Out, Err> = Result<<M as Mode>::Output<Out>, Located<Err>>;

/// The result of running a [`Parser`]. Can be converted into a [`Result`] via
/// [`ParseResult::into_result`] for when you only care about success or failure, or into distinct
/// error and output via [`ParseResult::into_output_errors`]
#[derive(Debug, Clone, PartialEq)]
pub struct ParseResult<T, E> {
    output: Option<T>,
    errs: Vec<E>,
}

impl<T, E> ParseResult<T, E> {
    pub(crate) fn new(output: Option<T>, errs: Vec<E>) -> ParseResult<T, E> {
        ParseResult { output, errs }
    }

    /// Whether this result contains output
    pub fn has_output(&self) -> bool {
        self.output.is_some()
    }

    /// Whether this result has any errors
    pub fn has_errors(&self) -> bool {
        !self.errs.is_empty()
    }

    /// Get a reference to the output of this result, if it exists
    pub fn output(&self) -> Option<&T> {
        self.output.as_ref()
    }

    /// Get a slice containing the parse errors for this result. The slice will be empty
    /// if there are no errors.
    pub fn errors(&self) -> impl ExactSizeIterator<Item = &E> {
        self.errs.iter()
    }

    /// Convert this `ParseResult` into an option containing the output, if any exists
    pub fn into_output(self) -> Option<T> {
        self.output
    }

    /// Convert this `ParseResult` into a vector containing any errors. The vector will be empty
    /// if there were no errors.
    pub fn into_errors(self) -> Vec<E> {
        self.errs
    }

    /// Convert this `ParseResult` into a tuple containing the output, if any existed, and errors,
    /// if any were encountered. This matches the output of the old [`Parser::parse_recovery`].
    pub fn into_output_errors(self) -> (Option<T>, Vec<E>) {
        (self.output, self.errs)
    }

    /// Convert this `ParseResult` into a standard `Result`. This discards output if parsing
    /// generated any errors, matching the old behavior of [`Parser::parse`].
    pub fn into_result(self) -> Result<T, Vec<E>> {
        if self.errs.is_empty() {
            self.output.ok_or(self.errs)
        } else {
            Err(self.errs)
        }
    }
}

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

        fn invoke<'a, In, Out, Err, State, Ctx, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, In, Err, State, Ctx>,
        ) -> PResult<Self, Out, Err>
        where
            In: Input + ?Sized,
            Err: Error<In>,
            State: 'a,
            P: Parser<'a, In, Out, Err, State, Ctx> + ?Sized;

        fn invoke_cfg<'a, In, Out, Err, State, Ctx, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, In, Err, State, Ctx>,
            cfg: P::Config,
        ) -> PResult<Self, Out, Err>
        where
            In: Input + ?Sized,
            Err: Error<In>,
            State: 'a,
            P: Parser<'a, In, Out, Err, State, Ctx> + ?Sized;
    }

    pub struct Emit;
    impl Mode for Emit {
        type Output<T> = T;
        #[inline(always)]
        fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T> {
            f()
        }
        #[inline(always)]
        fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> {
            f(x)
        }
        #[inline(always)]
        fn combine<T, U, V, F: FnOnce(T, U) -> V>(
            x: Self::Output<T>,
            y: Self::Output<U>,
            f: F,
        ) -> Self::Output<V> {
            f(x, y)
        }
        #[inline(always)]
        fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]> {
            x
        }

        #[inline(always)]
        fn invoke<'a, In, Out, Err, State, Ctx, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, In, Err, State, Ctx>,
        ) -> PResult<Self, Out, Err>
        where
            In: Input + ?Sized,
            Err: Error<In>,
            State: 'a,
            P: Parser<'a, In, Out, Err, State, Ctx> + ?Sized,
        {
            parser.go_emit(inp)
        }

        fn invoke_cfg<'a, In, Out, Err, State, Ctx, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, In, Err, State, Ctx>,
            cfg: P::Config,
        ) -> PResult<Self, Out, Err>
        where
            In: Input + ?Sized,
            Err: Error<In>,
            State: 'a,
            P: Parser<'a, In, Out, Err, State, Ctx> + ?Sized,
        {
            parser.go_cfg_emit(inp, cfg)
        }
    }

    pub struct Check;
    impl Mode for Check {
        type Output<T> = ();
        #[inline(always)]
        fn bind<T, F: FnOnce() -> T>(_: F) -> Self::Output<T> {}
        #[inline(always)]
        fn map<T, U, F: FnOnce(T) -> U>(_: Self::Output<T>, _: F) -> Self::Output<U> {}
        #[inline(always)]
        fn combine<T, U, V, F: FnOnce(T, U) -> V>(
            _: Self::Output<T>,
            _: Self::Output<U>,
            _: F,
        ) -> Self::Output<V> {
        }
        #[inline(always)]
        fn array<T, const N: usize>(_: [Self::Output<T>; N]) -> Self::Output<[T; N]> {}

        #[inline(always)]
        fn invoke<'a, In, Out, Err, State, Ctx, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, In, Err, State, Ctx>,
        ) -> PResult<Self, Out, Err>
        where
            In: Input + ?Sized,
            Err: Error<In>,
            State: 'a,
            P: Parser<'a, In, Out, Err, State, Ctx> + ?Sized,
        {
            parser.go_check(inp)
        }

        fn invoke_cfg<'a, In, Out, Err, State, Ctx, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, In, Err, State, Ctx>,
            cfg: P::Config,
        ) -> PResult<Self, Out, Err>
        where
            In: Input + ?Sized,
            Err: Error<In>,
            State: 'a,
            P: Parser<'a, In, Out, Err, State, Ctx> + ?Sized,
        {
            parser.go_cfg_check(inp, cfg)
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
        message = "`{Self}` is not a parser from `{In}` to `{Out}`",
        label = "This parser is not compatible because it does not implement `Parser<{In}, {Out}>`",
        note = "You should check that the output types of your parsers are consistent with combinator you're using",
    )
)]
pub trait Parser<
    'a,
    // The type of input the parser takes - commonly `str` or `[T]`
    In: Input + ?Sized,
    // The output type of the parser, when it succeeds
    Out,
    // The error type of the parser
    Err: Error<In>,
    // Global state - this can pass information up the parse chain
    State: 'a,
    // Local context - this can pass information down the parse chain, and be used to configure
    // parsers based of prior results.
    Ctx,
> {
    /// Type used to configure this parser - `()` if the parser takes no configuration
    type Config: Default;

    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way.
    ///
    /// If `None` is returned (i.e: parsing failed) then there will *always* be at least one item in the error `Vec`.
    /// If you want to include non-default state, use [`Parser::parse_with_state`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[I]`], a [`&str`], or anything implementing [`Stream`] to it.
    fn parse(&self, input: &'a In) -> ParseResult<Out, Err>
    where
        Self: Sized,
        State: Default,
        Ctx: Default,
    {
        self.parse_with_state(input, &mut State::default())
    }

    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way.
    /// The provided state will be passed on to parsers that expect it, such as [`map_with_state`](Parser::map_with_state).
    ///
    /// If `None` is returned (i.e: parsing failed) then there will *always* be at least one item in the error `Vec`.
    /// If you want to just use a default state value, use [`Parser::parse`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[I]`], a [`&str`], or anything implementing [`Stream`] to it.
    fn parse_with_state(&self, input: &'a In, state: &mut State) -> ParseResult<Out, Err>
    where
        Self: Sized,
        Ctx: Default,
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
        ParseResult::new(out, errs)
    }

    /// Parse a stream of tokens, ignoring any output, and returning any errors encountered along the way.
    ///
    /// If parsing failed, then there will *always* be at least one item in the returned `Vec`.
    /// If you want to include non-default state, use [`Parser::check_with_state`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[I]`], a [`&str`], or anything implementing [`Stream`] to it.
    fn check(&self, input: &'a In) -> ParseResult<(), Err>
    where
        Self: Sized,
        State: Default,
        Ctx: Default,
    {
        self.check_with_state(input, &mut State::default())
    }

    /// Parse a stream of tokens, ignoring any output, and returning any errors encountered along the way.
    ///
    /// If parsing failed, then there will *always* be at least one item in the returned `Vec`.
    /// If you want to just use a default state value, use [`Parser::check`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[I]`], a [`&str`], or anything implementing [`Stream`] to it.
    fn check_with_state(&self, input: &'a In, state: &mut State) -> ParseResult<(), Err>
    where
        Self: Sized,
        Ctx: Default,
    {
        let mut inp = InputRef::new(input, state);
        let res = self.go::<Check>(&mut inp);
        let mut errs = inp.into_errs();
        let out = match res {
            Ok(_) => Some(()),
            Err(e) => {
                errs.push(e.err);
                None
            }
        };
        ParseResult::new(out, errs)
    }

    /// Parse a stream with all the bells & whistles. You can use this to implement your own parser combinators. Note
    /// that both the signature and semantic requirements of this function are very likely to change in later versions.
    /// Where possible, prefer more ergonomic combinators provided elsewhere in the crate rather than implementing your
    /// own. For example, [`custom`] provides a flexible, ergonomic way API for process input streams that likely
    /// covers your use-case.
    #[doc(hidden)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err>
    where
        Self: Sized;

    #[doc(hidden)]
    fn go_emit(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<Emit, Out, Err>;
    #[doc(hidden)]
    fn go_check(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<Check, Out, Err>;

    /// TODO
    fn go_cfg<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>, cfg: Self::Config) -> PResult<M, Out, Err>
    where
        Self: Sized,
    {
        #![allow(unused_variables)]
        Self::go::<M>(self, inp)
    }

    #[doc(hidden)]
    fn go_cfg_emit(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>, cfg: Self::Config) -> PResult<Emit, Out, Err>;
    #[doc(hidden)]
    fn go_cfg_check(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>, cfg: Self::Config) -> PResult<Check, Out, Err>;

    /// TODO
    fn configure<F>(self, cfg: F) -> Configure<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Config, &Ctx) -> Self::Config,
    {
        Configure {
            parser: self,
            cfg,
        }
    }

    /// Map from a slice of the input based on the current parser's span to a value.
    ///
    /// The returned value may borrow data from the input slice, making this function very useful
    /// for creating zero-copy AST output values
    fn map_slice<U, F: Fn(&'a In::Slice) -> U>(self, f: F) -> MapSlice<'a, Self, In, Out, Err, State, Ctx, F, U>
    where
        Self: Sized,
        In: SliceInput,
        In::Slice: 'a,
    {
        MapSlice {
            parser: self,
            mapper: f,
            phantom: PhantomData,
        }
    }

    /// Convert the output of this parser into a slice of the input, based on the current parser's
    /// span.
    ///
    /// This is effectively a special case of [`map_slice`](Parser::map_slice)`(|x| x)`
    fn slice(self) -> Slice<Self, Out>
    where
        Self: Sized,
    {
        Slice {
            parser: self,
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
    /// let lowercase = any::<_, Simple<str>, (), ()>()
    ///     .filter(char::is_ascii_lowercase)
    ///     .repeated()
    ///     .at_least(1)
    ///     .collect::<String>()
    ///     .then_ignore(end());
    ///
    /// assert_eq!(lowercase.parse("hello").into_result(), Ok("hello".to_string()));
    /// assert!(lowercase.parse("Hello").has_errors());
    /// ```
    fn filter<F: Fn(&Out) -> bool>(self, f: F) -> Filter<Self, F>
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
    /// let word = any::<_, Simple<str>, (), ()>()
    ///     .filter(|c: &char| c.is_alphabetic())
    ///     .repeated().at_least(1)
    ///     .collect::<String>()
    ///     .map(Token::Word);
    ///
    /// let num = any()
    ///     .filter(|c: &char| c.is_ascii_digit())
    ///     .repeated().at_least(1)
    ///     .collect::<String>()
    ///     .map(|s| Token::Num(s.parse().unwrap()));
    ///
    /// let token = word.or(num);
    ///
    /// assert_eq!(token.parse("test").into_result(), Ok(Token::Word("test".to_string())));
    /// assert_eq!(token.parse("42").into_result(), Ok(Token::Num(42)));
    /// ```
    fn map<U, F: Fn(Out) -> U>(self, f: F) -> Map<Self, Out, F>
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
    /// # use chumsky::zero_copy::prelude::*;
    /// use std::ops::Range;
    ///
    /// // It's common for AST nodes to use a wrapper type that allows attaching span information to them
    /// #[derive(Debug, PartialEq)]
    /// pub struct Spanned<T>(T, SimpleSpan<usize>);
    ///
    /// let ident = text::ident::<_, _, Simple<str>, (), ()>()
    ///     .map_with_span(|ident, span| Spanned(ident, span))
    ///     .padded();
    ///
    /// assert_eq!(ident.parse("hello").into_result(), Ok(Spanned("hello", (0..5).into())));
    /// assert_eq!(ident.parse("       hello   ").into_result(), Ok(Spanned("hello", (7..12).into())));
    /// ```
    fn map_with_span<U, F: Fn(Out, In::Span) -> U>(self, f: F) -> MapWithSpan<Self, Out, F>
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
    /// # use chumsky::zero_copy::prelude::*;
    /// use std::ops::Range;
    ///
    /// // It's common for AST nodes to use a wrapper type that allows attaching span information to them
    /// #[derive(Debug, PartialEq)]
    /// pub struct Spanned<T>(T, SimpleSpan<usize>);
    ///
    /// let ident = text::ident::<_, _, Simple<str>, (), ()>()
    ///     .map_with_span(|ident, span| Spanned(ident, span))
    ///     .padded();
    ///
    /// assert_eq!(ident.parse("hello").into_result(), Ok(Spanned("hello", (0..5).into())));
    /// assert_eq!(ident.parse("       hello   ").into_result(), Ok(Spanned("hello", (7..12).into())));
    /// ```
    fn map_with_state<U, F: Fn(Out, In::Span, &mut State) -> U>(self, f: F) -> MapWithState<Self, Out, F>
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
    /// # use chumsky::zero_copy::prelude::*;
    /// let byte = text::int::<_, _, Rich<str>, (), ()>(10)
    ///     .try_map(|s, span| s
    ///         .parse::<u8>()
    ///         .map_err(|e| Rich::custom(span, e)));
    ///
    /// assert!(byte.parse("255").has_output());
    /// assert!(byte.parse("256").has_errors()); // Out of range
    /// ```
    #[doc(alias = "filter_map")]
    fn try_map<U, F: Fn(Out, In::Span) -> Result<U, Err>>(self, f: F) -> TryMap<Self, Out, F>
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
    fn try_map_with_state<U, F: Fn(Out, In::Span, &mut State) -> Result<U, Err>>(
        self,
        f: F,
    ) -> TryMapWithState<Self, Out, F>
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// // A parser that parses any number of whitespace characters without allocating
    /// let whitespace = any::<_, Simple<str>, (), ()>()
    ///     .filter(|c: &char| c.is_whitespace())
    ///     .ignored()
    ///     .repeated()
    ///     .collect::<Vec<_>>();
    ///
    /// assert_eq!(whitespace.parse("    ").into_result(), Ok(vec![(); 4]));
    /// assert_eq!(whitespace.parse("  hello").into_result(), Ok(vec![(); 2]));
    /// ```
    fn ignored(self) -> Ignored<Self, Out>
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// #[derive(Clone, Debug, PartialEq)]
    /// enum Op { Add, Sub, Mul, Div }
    ///
    /// let op = just::<_, _, Simple<str>, (), ()>('+').to(Op::Add)
    ///     .or(just('-').to(Op::Sub))
    ///     .or(just('*').to(Op::Mul))
    ///     .or(just('/').to(Op::Div));
    ///
    /// assert_eq!(op.parse("+").into_result(), Ok(Op::Add));
    /// assert_eq!(op.parse("/").into_result(), Ok(Op::Div));
    /// ```
    fn to<U: Clone>(self, to: U) -> To<Self, Out, U, Err, State>
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let word = any::<_, Simple<str>, (), ()>()
    ///     .filter(|c: &char| c.is_alphabetic())
    ///     .repeated()
    ///     .at_least(1)
    ///     .collect::<String>();
    /// let two_words = word.then_ignore(just(' ')).then(word);
    ///
    /// assert_eq!(two_words.parse("dog cat").into_result(), Ok(("dog".to_string(), "cat".to_string())));
    /// assert!(two_words.parse("hedgehog").has_errors());
    /// ```
    fn then<U, B: Parser<'a, In, U, Err, State, Ctx>>(self, other: B) -> Then<Self, B, Out, U, Err, State>
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let zeroes = any::<_, Simple<str>, (), ()>().filter(|c: &char| *c == '0').ignored().repeated().collect::<Vec<_>>();
    /// let digits = any().filter(|c: &char| c.is_ascii_digit()).repeated().collect::<Vec<_>>();
    /// let integer = zeroes
    ///     .ignore_then(digits)
    ///     .collect::<String>()
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// assert_eq!(integer.parse("00064").into_result(), Ok(64));
    /// assert_eq!(integer.parse("32").into_result(), Ok(32));
    /// ```
    fn ignore_then<U, B: Parser<'a, In, U, Err, State, Ctx>>(self, other: B) -> IgnoreThen<Self, B, Out, Err, State>
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let word = any::<_, Simple<str>, (), ()>()
    ///     .filter(|c: &char| c.is_alphabetic())
    ///     .repeated()
    ///     .at_least(1)
    ///     .collect::<String>();
    ///
    /// let punctuated = word
    ///     .then_ignore(just('!').or(just('?')).or_not());
    ///
    /// let sentence = punctuated
    ///     .padded() // Allow for whitespace gaps
    ///     .repeated()
    ///     .collect::<Vec<_>>();
    ///
    /// assert_eq!(
    ///     sentence.parse("hello! how are you?").into_result(),
    ///     Ok(vec![
    ///         "hello".to_string(),
    ///         "how".to_string(),
    ///         "are".to_string(),
    ///         "you".to_string(),
    ///     ]),
    /// );
    /// ```
    fn then_ignore<U, B: Parser<'a, In, U, Err, State, Ctx>>(self, other: B) -> ThenIgnore<Self, B, U, Err, State>
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// // A parser that parses a single letter and then its successor
    /// let successive_letters = one_of::<_, _, Simple<[u8]>, (), ()>(b'a'..=b'z')
    ///     .then_with_ctx(
    ///         just(b'\0').configure(|cfg, ctx: &u8| cfg.set_seq(*ctx + 1)),
    ///         |letter, _| letter,
    ///     );
    ///
    /// assert_eq!(successive_letters.parse(b"ab").into_result(), Ok(b'b')); // 'b' follows 'a'
    /// assert!(successive_letters.parse(b"ac").has_errors()); // 'c' does not follow 'a'
    /// ```
    fn then_with_ctx<U, CtxN, P, F>(
        self,
        then: P,
        make_ctx: F,
    ) -> ThenWithCtx<Self, P, Out, F, In, Err, State, CtxN>
    where
        Self: Sized,
        P: Parser<'a, In, U, Err, State, CtxN>,
        F: Fn(Out, &Ctx) -> CtxN,
    {
        ThenWithCtx {
            parser: self,
            then,
            make_ctx,
            phantom: PhantomData,
        }
    }

    /// ```
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    ///
    /// // Lua-style multiline string literal
    /// let string = just::<_, _, Simple<str>, (), ()>('=')
    ///     .repeated()
    ///     .map_slice(str::len)
    ///     .padded_by(just('['))
    ///     .then_with_ctx(
    ///         {
    ///             let close = just('=').repeated().configure(|cfg, n| cfg.exactly(*n)).padded_by(just(']'));
    ///             any()
    ///                 .and_is(close.not())
    ///                 .repeated()
    ///                 .slice()
    ///                 .then_ignore(close)
    ///         },
    ///         |n, _| n,
    ///     );
    ///
    /// assert_eq!(
    ///     string.parse("[[wxyz]]").into_result(),
    ///     Ok("wxyz"),
    /// );
    /// assert_eq!(
    ///     string.parse("[==[abcd]=]efgh]===]ijkl]==]").into_result(),
    ///     Ok("abcd]=]efgh]===]ijkl"),
    /// );
    /// ```
    fn and_is<U, B>(self, other: B) -> AndIs<Self, B, U>
    where
        Self: Sized,
        B: Parser<'a, In, U, Err, State, Ctx>,
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// // A LISP-style S-expression
    /// #[derive(Debug, PartialEq)]
    /// enum SExpr {
    ///     Ident(String),
    ///     Num(u64),
    ///     List(Vec<SExpr>),
    /// }
    ///
    /// let ident = any::<_, Simple<str>, (), ()>().filter(|c: &char| c.is_alphabetic())
    ///     .repeated()
    ///     .at_least(1)
    ///     .collect::<String>();
    ///
    /// let num = text::int(10)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let s_expr = recursive(|s_expr| s_expr
    ///     .padded()
    ///     .repeated()
    ///     .collect::<Vec<_>>()
    ///     .map(SExpr::List)
    ///     .delimited_by(just('('), just(')'))
    ///     .or(ident.map(SExpr::Ident))
    ///     .or(num.map(SExpr::Num)));
    ///
    /// // A valid input
    /// assert_eq!(
    ///     s_expr.parse("(add (mul 42 3) 15)").into_result(),
    ///     Ok(SExpr::List(vec![
    ///         SExpr::Ident("add".to_string()),
    ///         SExpr::List(vec![
    ///             SExpr::Ident("mul".to_string()),
    ///             SExpr::Num(42),
    ///             SExpr::Num(3),
    ///         ]),
    ///         SExpr::Num(15),
    ///     ])),
    /// );
    /// ```
    fn delimited_by<U, V, B, C>(self, start: B, end: C) -> DelimitedBy<Self, B, C, U, V>
    where
        Self: Sized,
        B: Parser<'a, In, U, Err, State, Ctx>,
        C: Parser<'a, In, V, Err, State, Ctx>,
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let ident = text::ident::<_, _, Simple<str>, (), ()>()
    ///     .padded_by(just('!'));
    ///
    /// assert_eq!(ident.parse("!hello!").into_result(), Ok("hello"));
    /// assert!(ident.parse("hello!").has_errors());
    /// assert!(ident.parse("!hello").has_errors());
    /// assert!(ident.parse("hello").has_errors());
    /// ```
    fn padded_by<U, B>(self, padding: B) -> PaddedBy<Self, B, U>
    where
        Self: Sized,
        B: Parser<'a, In, U, Err, State, Ctx>,
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let op = just::<_, _, Simple<str>, (), ()>('+')
    ///     .or(just('-'))
    ///     .or(just('*'))
    ///     .or(just('/'));
    ///
    /// assert_eq!(op.parse("+").into_result(), Ok('+'));
    /// assert_eq!(op.parse("/").into_result(), Ok('/'));
    /// assert!(op.parse("!").has_errors());
    /// ```
    fn or<B>(self, other: B) -> Or<Self, B>
    where
        Self: Sized,
        B: Parser<'a, In, Out, Err, State, Ctx>,
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let word = any::<_, Simple<str>, (), ()>().filter(|c: &char| c.is_alphabetic())
    ///     .repeated()
    ///     .at_least(1)
    ///     .collect::<String>();
    ///
    /// let word_or_question = word
    ///     .then(just('?').or_not());
    ///
    /// assert_eq!(word_or_question.parse("hello?").into_result(), Ok(("hello".to_string(), Some('?'))));
    /// assert_eq!(word_or_question.parse("wednesday").into_result(), Ok(("wednesday".to_string(), None)));
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
    /// let tree = recursive::<_, _, Simple<str>, (), (), _, _>(|tree| {
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
    ///     tree.parse("{abcd{efg{hijk}lmn{opq}rs}tuvwxyz}").into_result(),
    ///     Ok(Tree::Group(vec![
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
    fn not(self) -> Not<Self, Out>
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let num = any::<_, Simple<str>, (), ()>()
    ///     .filter(|c: &char| c.is_ascii_digit())
    ///     .repeated()
    ///     .at_least(1)
    ///     .collect::<String>()
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let sum = num.clone().then(just('+').ignore_then(num).repeated().collect::<Vec<_>>())
    ///     .foldl(|a, b| a + b);
    ///
    /// assert_eq!(sum.parse("2+13+4+0+5").into_result(), Ok(24));
    /// ```
    fn repeated(self) -> Repeated<Self, Out, In, (), Err, State, Ctx>
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
    /// Input is eagerly parsed. Consider using [`RepeatedExactly::repeated`] if a non-constant number of values are expected.
    ///
    /// The output type of this parser can be any [`ContainerExactly`].
    fn repeated_exactly<const N: usize>(self) -> RepeatedExactly<Self, Out, (), N>
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let shopping = text::ident::<_, _, Simple<str>, (), ()>()
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .collect::<Vec<_>>();
    ///
    /// assert_eq!(shopping.parse("eggs").into_result(), Ok(vec!["eggs"]));
    /// assert_eq!(shopping.parse("eggs, flour, milk").into_result(), Ok(vec!["eggs", "flour", "milk"]));
    /// ```
    ///
    /// See [`SeparatedBy::allow_leading`] and [`SeparatedBy::allow_trailing`] for more examples.
    fn separated_by<U, B>(self, separator: B) -> SeparatedBy<Self, B, Out, U, In, (), Err, State, Ctx>
    where
        Self: Sized,
        B: Parser<'a, In, U, Err, State, Ctx>,
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
    /// You can use [`SeparatedByExactly::allow_leading`] or [`SeparatedByExactly::allow_trailing`] to
    /// allow leading or trailing separators.
    ///
    /// The output type of this parser can be any [`ContainerExactly`].
    fn separated_by_exactly<U, B, const N: usize>(
        self,
        separator: B,
    ) -> SeparatedByExactly<Self, B, U, (), N>
    where
        Self: Sized,
        B: Parser<'a, In, U, Err, State, Ctx>,
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let int = text::int::<_, _, Simple<str>, (), ()>(10)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let signed = just('+').to(1)
    ///     .or(just('-').to(-1))
    ///     .repeated()
    ///     .collect::<Vec<_>>()
    ///     .then(int)
    ///     .foldr(|a, b| a * b);
    ///
    /// assert_eq!(signed.parse("3").into_result(), Ok(3));
    /// assert_eq!(signed.parse("-17").into_result(), Ok(-17));
    /// assert_eq!(signed.parse("--+-+-5").into_result(), Ok(5));
    /// ```
    fn foldr<A, B, F>(self, f: F) -> Foldr<Self, F, A, B, Err, State>
    where
        Self: Parser<'a, In, (A, B), Err, State, Ctx> + Sized,
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let int = text::int::<_, _, Simple<str>, (), ()>(10)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let sum = int
    ///     .clone()
    ///     .then(just('+').ignore_then(int).repeated().collect::<Vec<_>>())
    ///     .foldl(|a, b| a + b);
    ///
    /// assert_eq!(sum.parse("1+12+3+9").into_result(), Ok(25));
    /// assert_eq!(sum.parse("6").into_result(), Ok(6));
    /// ```
    fn foldl<A, B, F>(self, f: F) -> Foldl<Self, F, A, B, Err, State>
    where
        Self: Parser<'a, In, (A, B), Err, State, Ctx> + Sized,
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
    /// # use chumsky::zero_copy::prelude::*;
    /// let just_numbers = text::digits::<_, _, Simple<str>, (), ()>(10)
    ///     .padded()
    ///     .then_ignore(none_of("+-*/").rewind())
    ///     .separated_by(just(','))
    ///     .collect::<Vec<_>>();
    /// // 3 is not parsed because it's followed by '+'.
    /// assert_eq!(just_numbers.parse("1, 2, 3 + 4").into_result(), Ok(vec!["1", "2"]));
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
    /// # use chumsky::zero_copy::prelude::*;
    /// let ident = text::ident::<_, _, Simple<str>, (), ()>().padded();
    ///
    /// // A pattern with no whitespace surrounding it is accepted
    /// assert_eq!(ident.parse("hello").into_result(), Ok("hello"));
    /// // A pattern with arbitrary whitespace surrounding it is also accepted
    /// assert_eq!(ident.parse(" \t \n  \t   world  \t  ").into_result(), Ok("world"));
    /// ```
    fn padded(self) -> Padded<Self>
    where
        Self: Sized,
        In: Input,
        In::Token: Char,
    {
        Padded { parser: self }
    }

    /// Flatten a nested collection.
    ///
    /// This use-cases of this method are broadly similar to those of [`Iterator::flatten`].
    ///
    /// The output type of this parser is `Vec<T>`, where the original parser output was
    /// `impl IntoIterator<Item = impl IntoIterator<Item = T>>`.
    fn flatten<T, Inner>(self) -> Map<Self, Out, fn(Out) -> Vec<T>>
    where
        Self: Sized,
        Out: IntoIterator<Item = Inner>,
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// #[derive(Debug, PartialEq)]
    /// enum Expr<'a> {
    ///     Error,
    ///     Int(&'a str),
    ///     List(Vec<Expr<'a>>),
    /// }
    ///
    /// let recover = just('[')
    ///         .ignore_then(take_until(just(']')).ignored());
    ///
    /// let expr = recursive::<_, _, Simple<str>, (), (), _, _>(|expr| expr
    ///     .separated_by(just(','))
    ///     .collect::<Vec<_>>()
    ///     .delimited_by(just('['), just(']'))
    ///     .map(Expr::List)
    ///     // If parsing a list expression fails, recover at the next delimiter, generating an error AST node
    ///     .recover_with(recover.map(|_| Expr::Error))
    ///     .or(text::int(10).map(Expr::Int))
    ///     .padded());
    ///
    /// assert!(expr.parse("five").has_errors()); // Text is not a valid expression in this language...
    /// assert_eq!(
    ///     expr.parse("[1, 2, 3]").into_result(),
    ///     Ok(Expr::List(vec![Expr::Int("1"), Expr::Int("2"), Expr::Int("3")])),
    /// ); // ...but lists and numbers are!
    ///
    /// // This input has two syntax errors...
    /// let res = expr.parse("[[1, two], [3, four]]");
    /// // ...and error recovery allows us to catch both of them!
    /// assert_eq!(res.errors().len(), 2);
    /// // Additionally, the AST we get back still has useful information.
    /// assert_eq!(res.output(), Some(&Expr::List(vec![Expr::Error, Expr::Error])));
    /// ```
    fn recover_with<F: Parser<'a, In, Out, Err, State, Ctx>>(self, fallback: F) -> RecoverWith<Self, F>
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
        F: Fn(Err) -> Err,
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
        F: Fn(Err, In::Span) -> Err,
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
        F: Fn(Err, In::Span, &mut State) -> Err,
    {
        MapErrWithState {
            parser: self,
            mapper: f,
        }
    }

    /// Validate an output, producing non-terminal errors if it does not fulfil certain criteria.
    ///
    /// This function also permits mapping the output to a value of another type, similar to [`Parser::map`].
    ///
    /// If you wish parsing of this pattern to halt when an error is generated instead of continuing, consider using
    /// [`Parser::try_map`] instead.
    ///
    /// The output type of this parser is `U`, the result of the validation closure.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::zero_copy::prelude::*;
    /// let large_int = text::int::<_, _, Rich<str>, (), ()>(10)
    ///     .from_str()
    ///     .unwrapped()
    ///     .validate(|x: u32, span, emitter| {
    ///         if x < 256 { emitter.emit(Rich::custom(span, format!("{} must be 256 or higher.", x))) }
    ///         x
    ///     });
    ///
    /// assert_eq!(large_int.parse("537").into_result(), Ok(537));
    /// assert!(large_int.parse("243").into_result().is_err());
    /// ```
    fn validate<U, F>(self, f: F) -> Validate<Self, Out, F>
    where
        Self: Sized,
        F: Fn(Out, In::Span, &mut Emitter<Err>) -> U,
    {
        Validate {
            parser: self,
            validator: f,
            phantom: PhantomData,
        }
    }

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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let word = any::<_, Simple<str>, (), ()>().filter(|c: &char| c.is_alphabetic()) // This parser produces an output of `char`
    ///     .repeated() // This parser produces an output of `Vec<char>`
    ///     .collect::<String>(); // But `Vec<char>` is less useful than `String`, so convert to the latter
    ///
    /// assert_eq!(word.parse("hello").into_result(), Ok("hello".to_string()));
    /// ```
    // TODO: Make `Parser::repeated` generic over an `impl FromIterator` to reduce required allocations
    fn collect<C>(self) -> Map<Self, Out, fn(Out) -> C>
    where
        Self: Sized,
        Out: IntoIterator,
        C: FromIterator<<Out as IntoIterator>::Item>,
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
    /// # use chumsky::zero_copy::{prelude::*, error::Simple};
    /// let int = just::<_, _, Simple<str>, (), ()>('-').or_not()
    ///     .chain(any().filter(|c: &char| c.is_ascii_digit() && *c != '0')
    ///         .chain(any().filter(|c: &char| c.is_ascii_digit()).repeated().collect::<Vec<_>>()))
    ///     .or(just('0').map(|c| vec![c]))
    ///     .then_ignore(end())
    ///     .collect::<String>()
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// assert_eq!(int.parse("0").into_result(), Ok(0));
    /// assert_eq!(int.parse("415").into_result(), Ok(415));
    /// assert_eq!(int.parse("-50").into_result(), Ok(-50));
    /// assert!(int.parse("-0").has_errors());
    /// assert!(int.parse("05").has_errors());
    /// ```
    fn chain<T, U, P>(
        self,
        other: P,
    ) -> Map<Then<Self, P, Out, U, Err, State>, (Out, U), fn((Out, U)) -> Vec<T>>
    where
        Self: Sized,
        Out: Chain<T>,
        U: Chain<T>,
        P: Parser<'a, In, U, Err, State, Ctx>,
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
        F: Fn(Err) -> Result<Out, Err>,
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
    /// # use chumsky::zero_copy::prelude::*;
    /// let uint64 = text::int::<_, _, Simple<str>, (), ()>(10)
    ///     .from_str::<u64>()
    ///     .unwrapped();
    ///
    /// assert_eq!(uint64.parse("7").into_result(), Ok(7));
    /// assert_eq!(uint64.parse("42").into_result(), Ok(42));
    /// ```
    #[allow(clippy::wrong_self_convention)]
    fn from_str<U>(self) -> Map<Self, Out, fn(Out) -> Result<U, U::Err>>
    where
        Self: Sized,
        U: FromStr,
        Out: AsRef<str>,
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
    /// # use chumsky::zero_copy::prelude::*;
    /// let boolean = just::<_, _, Simple<str>, (), ()>("true")
    ///     .or(just("false"))
    ///     .from_str::<bool>()
    ///     .unwrapped(); // Cannot panic: the only possible outputs generated by the parser are "true" or "false"
    ///
    /// assert_eq!(boolean.parse("true").into_result(), Ok(true));
    /// assert_eq!(boolean.parse("false").into_result(), Ok(false));
    /// // Does not panic, because the original parser only accepts "true" or "false"
    /// assert!(boolean.parse("42").has_errors());
    /// ```
    fn unwrapped<U, E1>(self) -> Map<Self, Result<U, E1>, fn(Result<U, E1>) -> U>
    where
        Self: Sized + Parser<'a, In, Result<U, E1>, Err, State, Ctx>,
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
    fn boxed(self) -> Boxed<'a, In, Out, Err, State, Ctx, Self::Config>
    where
        Self: Sized + 'a,
    {
        Boxed {
            inner: Rc::new(self),
        }
    }
}

/// See [`Parser::boxed`].
///
/// This type is a [`repr(transparent)`](https://doc.rust-lang.org/nomicon/other-reprs.html#reprtransparent) wrapper
/// around its inner value.
///
/// Due to current implementation details, the inner value is not, in fact, a [`Box`], but is an [`Rc`] to facilitate
/// efficient cloning. This is likely to change in the future. Unlike [`Box`], [`Rc`] has no size guarantees: although
/// it is *currently* the same size as a raw pointer.
// TODO: Don't use an Rc
pub struct Boxed<'a, In: ?Sized, Out, Err, State = (), Ctx = (), Conf = ()> {
    inner: Rc<dyn Parser<'a, In, Out, Err, State, Ctx, Config = Conf> + 'a>,
}

impl<'a, In: ?Sized, Err, Out, State, Ctx> Clone for Boxed<'a, In, Out, Err, State, Ctx> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, In, Out, Err, State, Ctx, Conf> Parser<'a, In, Out, Err, State, Ctx> for Boxed<'a, In, Out, Err, State, Ctx, Conf>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    Conf: Default,
{
    type Config = Conf;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
        M::invoke(&*self.inner, inp)
    }

    fn go_cfg<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>, cfg: Self::Config) -> PResult<M, Out, Err> where Self: Sized {
        M::invoke_cfg(&*self.inner, inp, cfg)
    }

    go_extra!(Out);
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

    type Span = (FileId, SimpleSpan<usize>);

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
        parser().parse(&WithContext(42, r#"hello "world" these are "test" tokens"#))
            .into_result(),
        Ok([
            ((42, (0..5).into()), Token::Ident("hello")),
            ((42, (6..13).into()), Token::String("\"world\"")),
            ((42, (14..19).into()), Token::Ident("these")),
            ((42, (20..23).into()), Token::Ident("are")),
            ((42, (24..30).into()), Token::String("\"test\"")),
            ((42, (31..37).into()), Token::Ident("tokens")),
        ]),
    );
}

use combinator::MapSlice;
use crate::zero_copy::input::Emitter;

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
        parser().parse("[122 , 23,43,    4, ]").into_result(),
        Ok(vec![122, 23, 43, 4]),
    );
    assert_eq!(
        parser().parse("[0, 3, 6, 900,120]").into_result(),
        Ok(vec![0, 3, 6, 900, 120]),
    );
    assert_eq!(
        parser().parse("[200,400,50  ,0,0, ]").into_result(),
        Ok(vec![200, 400, 50, 0, 0]),
    );

    assert!(parser().parse("[1234,123,12,1]").has_errors());
    assert!(parser().parse("[,0, 1, 456]").has_errors());
    assert!(parser().parse("[3, 4, 5, 67 89,]").has_errors());
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
                .slice()
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
        parser().parse("abc 123 [").into_result(),
        Ok(("abc", 123, '[')),
    );
    assert_eq!(
        parser().parse("among3d").into_result(),
        Ok(("among", 3, 'd')),
    );
    assert_eq!(
        parser().parse("cba321,").into_result(),
        Ok(("cba", 321, ',')),
    );

    assert!(parser().parse("abc 123  ").has_errors());
    assert!(parser().parse("123abc ]").has_errors());
    assert!(parser().parse("and one &").has_errors());
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
    let mut input = InputRef::<_, EmptyErr, _, ()>::new(input, &mut state);

    while let (_, Some(c)) = input.next() {
        std::hint::black_box(c);
    }
}
