#![cfg_attr(not(any(doc, feature = "std", test)), no_std)]
#![cfg_attr(feature = "nightly", feature(never_type, once_cell, rustc_attrs))]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]

extern crate alloc;

macro_rules! go_extra {
    ( $O :ty ) => {
        #[inline(always)]
        fn go_emit(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Emit, $O> {
            Parser::<I, $O, E>::go::<Emit>(self, inp)
        }
        #[inline(always)]
        fn go_check(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Check, $O> {
            Parser::<I, $O, E>::go::<Check>(self, inp)
        }
    };
}

macro_rules! go_cfg_extra {
    ( $O :ty ) => {
        #[inline(always)]
        fn go_emit_cfg(
            &self,
            inp: &mut InputRef<'a, '_, I, E>,
            cfg: Self::Config,
        ) -> PResult<Emit, $O> {
            ConfigParser::<I, $O, E>::go_cfg::<Emit>(self, inp, cfg)
        }
        #[inline(always)]
        fn go_check_cfg(
            &self,
            inp: &mut InputRef<'a, '_, I, E>,
            cfg: Self::Config,
        ) -> PResult<Check, $O> {
            ConfigParser::<I, $O, E>::go_cfg::<Check>(self, inp, cfg)
        }
    };
}

mod blanket;
pub mod combinator;
pub mod container;
pub mod error;
pub mod extra;
pub mod input;
pub mod primitive;
pub mod recovery;
pub mod recursive;
#[cfg(feature = "regex")]
pub mod regex;
pub mod span;
mod stream;
pub mod text;
mod util;

/// Commonly used functions, traits and types.
///
/// *Listen, three eyes,” he said, “don’t you try to outweird me, I get stranger things than you free with my breakfast
/// cereal.”*
pub mod prelude {
    pub use super::{
        error::{Cheap, EmptyErr, Error as _, Rich, Simple},
        extra,
        input::Input,
        primitive::{any, choice, custom, empty, end, group, just, map_ctx, none_of, one_of, todo},
        recovery::{nested_delimiters, skip_then_retry_until, skip_until, via_parser},
        recursive::{recursive, Recursive},
        // select,
        span::{SimpleSpan, Span as _},
        text,
        Boxed,
        ConfigIterParser,
        ConfigParser,
        IterParser,
        ParseResult,
        Parser,
    };
    pub use crate::{select, select_ref};
}

use alloc::{
    boxed::Box,
    rc::{Rc, Weak},
    string::String,
    vec,
    vec::Vec,
};
use core::{
    borrow::Borrow,
    cmp::{Eq, Ordering, PartialEq},
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::MaybeUninit,
    ops::{Deref, Range, RangeFrom},
    panic::Location,
    str::FromStr,
};
use hashbrown::HashMap;

use self::{
    combinator::*,
    container::*,
    error::Error,
    extra::ParserExtra,
    input::{BorrowInput, Emitter, InputRef, SliceInput, StrInput, ValueInput},
    internal::{IPResult, PResult},
    prelude::*,
    primitive::Any,
    private::{Check, Emit, Mode},
    recovery::{RecoverWith, Strategy},
    span::Span,
    text::*,
    util::MaybeMut,
};
#[cfg(doc)]
use self::{primitive::custom, stream::Stream};

/// A type that can represent a borrowed reference to a `T` or a value of `T`.
///
/// Used internally to faciltitate zero-copy manipulation of tokens during error generation (see [`Error`]).
#[derive(Copy, Clone)]
pub enum MaybeRef<'a, T> {
    /// We have a reference to `T`.
    Ref(&'a T),
    /// We have a value of `T`.
    Val(T),
}

impl<'a, T: PartialEq> PartialEq for MaybeRef<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        &**self == &**other
    }
}

impl<'a, T: Eq> Eq for MaybeRef<'a, T> {}

impl<'a, T: Hash> Hash for MaybeRef<'a, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        T::hash(&**self, state)
    }
}

impl<'a, T: fmt::Debug> fmt::Debug for MaybeRef<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        T::fmt(&**self, f)
    }
}

impl<'a, T> MaybeRef<'a, T> {
    /// Convert this [`MaybeRef<T>`] into a `T`, cloning the inner value if necessary.
    pub fn into_inner(self) -> T
    where
        T: Clone,
    {
        match self {
            Self::Ref(x) => x.clone(),
            Self::Val(x) => x,
        }
    }
}

impl<'a, T> Deref for MaybeRef<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Ref(x) => *x,
            Self::Val(x) => x,
        }
    }
}

impl<'a, T> From<T> for MaybeRef<'a, T> {
    fn from(x: T) -> Self {
        Self::Val(x)
    }
}

impl<'a, T> From<&'a T> for MaybeRef<'a, T> {
    fn from(x: &'a T) -> Self {
        Self::Ref(x)
    }
}

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

    /// Get a slice containing the parse errors for this result. The slice will be empty if there are no errors.
    pub fn errors(&self) -> impl ExactSizeIterator<Item = &E> {
        self.errs.iter()
    }

    /// Convert this `ParseResult` into an option containing the output, if any exists
    pub fn into_output(self) -> Option<T> {
        self.output
    }

    /// Convert this `ParseResult` into a vector containing any errors. The vector will be empty if there were no
    /// errors.
    pub fn into_errors(self) -> Vec<E> {
        self.errs
    }

    /// Convert this `ParseResult` into a tuple containing the output, if any existed, and errors, if any were
    /// encountered.
    pub fn into_output_errors(self) -> (Option<T>, Vec<E>) {
        (self.output, self.errs)
    }

    /// Convert this `ParseResult` into a standard `Result`. This discards output if parsing generated any errors,
    /// matching the old behavior of [`Parser::parse`].
    pub fn into_result(self) -> Result<T, Vec<E>> {
        if self.errs.is_empty() {
            self.output.ok_or(self.errs)
        } else {
            Err(self.errs)
        }
    }
}

#[doc(hidden)]
#[derive(Clone)]
pub struct Located<E> {
    pos: usize,
    err: E,
}

impl<E> Located<E> {
    pub fn at(pos: usize, err: E) -> Self {
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

fn expect_end<'a, I: Input<'a>, E: ParserExtra<'a, I>>(
    inp: &mut InputRef<'a, '_, I, E>,
) -> PResult<Check, ()> {
    let before = inp.offset();
    match inp.next_maybe() {
        (_, None) => Ok(()),
        (_, Some(tok)) => {
            inp.emit(E::Error::expected_found(
                None,
                Some(tok.into()),
                // SAFETY: Using offsets derived from input
                unsafe { inp.span_since(before) },
            ));
            Ok(())
        }
    }
}

mod private {
    use super::*;

    pub trait ModeSealed {}

    impl ModeSealed for Emit {}
    impl ModeSealed for Check {}

    /// An abstract parse mode - can be [`Emit`] or [`Check`] in practice, and represents the
    /// common interface for handling both in the same method.
    pub trait Mode: ModeSealed {
        /// The output of this mode for a given type
        type Output<T>;

        /// Bind the result of a closure into an output
        fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T>;

        /// Given an [`Output`](Self::Output), takes its value and return a newly generated output
        fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U>;

        /// Given two [`Output`](Self::Output)s, take their values and combine them into a new
        /// output value
        fn combine<T, U, V, F: FnOnce(T, U) -> V>(
            x: Self::Output<T>,
            y: Self::Output<U>,
            f: F,
        ) -> Self::Output<V>;

        /// Given an array of outputs, bind them into an output of arrays
        fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]>;

        /// Invoke a parser user the current mode. This is normally equivalent to
        /// [`parser.go::<M>(inp)`](Parser::go), but it can be called on unsized values such as
        /// `dyn Parser`.
        fn invoke<'a, I, O, E, P>(parser: &P, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Self, O>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            P: Parser<'a, I, O, E> + ?Sized;

        /// Invoke a parser with configuration using the current mode. This is normally equivalent
        /// to [`parser.go::<M>(inp)`](ConfigParser::go_cfg), but it can be called on unsized values
        /// such as `dyn Parser`.
        fn invoke_cfg<'a, I, O, E, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, I, E>,
            cfg: P::Config,
        ) -> PResult<Self, O>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            P: ConfigParser<'a, I, O, E> + ?Sized;
    }

    /// Emit mode - generates parser output
    pub struct Emit;

    impl Mode for Emit {
        type Output<T> = T;
        #[inline]
        fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T> {
            f()
        }
        #[inline]
        fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> {
            f(x)
        }
        #[inline]
        fn combine<T, U, V, F: FnOnce(T, U) -> V>(
            x: Self::Output<T>,
            y: Self::Output<U>,
            f: F,
        ) -> Self::Output<V> {
            f(x, y)
        }
        #[inline]
        fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]> {
            x
        }

        #[inline]
        fn invoke<'a, I, O, E, P>(parser: &P, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Self, O>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            P: Parser<'a, I, O, E> + ?Sized,
        {
            parser.go_emit(inp)
        }

        #[inline]
        fn invoke_cfg<'a, I, O, E, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, I, E>,
            cfg: P::Config,
        ) -> PResult<Self, O>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            P: ConfigParser<'a, I, O, E> + ?Sized,
        {
            parser.go_emit_cfg(inp, cfg)
        }
    }

    /// Check mode - all output is discarded, and only uses parsers to check validity
    pub struct Check;

    impl Mode for Check {
        type Output<T> = ();
        #[inline]
        fn bind<T, F: FnOnce() -> T>(_: F) -> Self::Output<T> {}
        #[inline]
        fn map<T, U, F: FnOnce(T) -> U>(_: Self::Output<T>, _: F) -> Self::Output<U> {}
        #[inline]
        fn combine<T, U, V, F: FnOnce(T, U) -> V>(
            _: Self::Output<T>,
            _: Self::Output<U>,
            _: F,
        ) -> Self::Output<V> {
        }
        #[inline]
        fn array<T, const N: usize>(_: [Self::Output<T>; N]) -> Self::Output<[T; N]> {}

        #[inline]
        fn invoke<'a, I, O, E, P>(parser: &P, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Self, O>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            P: Parser<'a, I, O, E> + ?Sized,
        {
            parser.go_check(inp)
        }

        #[inline]
        fn invoke_cfg<'a, I, O, E, P>(
            parser: &P,
            inp: &mut InputRef<'a, '_, I, E>,
            cfg: P::Config,
        ) -> PResult<Self, O>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            P: ConfigParser<'a, I, O, E> + ?Sized,
        {
            parser.go_check_cfg(inp, cfg)
        }
    }
}

/// Internal API features not intended for general use.
///
/// **Please note that this module is exempt from the ordinary stability guarantees of the crate. You must not rely on
/// API features within this module unless you are happy for your code to break with only a minor version increment.**
pub mod internal {
    use super::*;
    pub use crate::input::SpannedTokenMaybe;
    pub use private::{Check, Emit, Mode};

    /// The result of calling [`Parser::go`]
    pub type PResult<M, O> = Result<<M as Mode>::Output<O>, ()>;
    /// The result of calling [`IterParser::next`]
    pub type IPResult<M, O> = Result<Option<<M as Mode>::Output<O>>, ()>;
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
pub trait Parser<'a, I: Input<'a>, O, E: ParserExtra<'a, I> = extra::Default> {
    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way.
    ///
    /// If `None` is returned (i.e: parsing failed) then there will *always* be at least one item in the error `Vec`.
    /// If you want to include non-default state, use [`Parser::parse_with_state`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[T]`], a [`&str`], [`Stream`], or anything implementing [`Input`] to it.
    fn parse(&self, input: I) -> ParseResult<O, E::Error>
    where
        Self: Sized,
        I: Input<'a>,
        E::State: Default,
        E::Context: Default,
    {
        self.parse_with_state(input, &mut E::State::default())
    }

    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way.
    /// The provided state will be passed on to parsers that expect it, such as [`map_with_state`](Parser::map_with_state).
    ///
    /// If `None` is returned (i.e: parsing failed) then there will *always* be at least one item in the error `Vec`.
    /// If you want to just use a default state value, use [`Parser::parse`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[T]`], a [`&str`], [`Stream`], or anything implementing [`Input`] to it.
    fn parse_with_state(&self, input: I, state: &mut E::State) -> ParseResult<O, E::Error>
    where
        Self: Sized,
        I: Input<'a>,
        E::Context: Default,
    {
        let ctx = E::Context::default();
        let mut inp = InputRef::new(&input, state, &ctx);
        let res = self.go::<Emit>(&mut inp);
        let res = res.and_then(|o| expect_end(&mut inp).map(move |()| o));
        let alt = inp.errors.alt.take();
        let mut errs = inp.into_errs();
        let out = match res {
            Ok(out) => Some(out),
            Err(()) => {
                errs.push(alt.expect("error but no alt?").err);
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
    /// [`&[T]`], a [`&str`], [`Stream`], or anything implementing [`Input`] to it.
    fn check(&self, input: I) -> ParseResult<(), E::Error>
    where
        Self: Sized,
        I: Input<'a>,
        E::State: Default,
        E::Context: Default,
    {
        self.check_with_state(input, &mut E::State::default())
    }

    /// Parse a stream of tokens, ignoring any output, and returning any errors encountered along the way.
    ///
    /// If parsing failed, then there will *always* be at least one item in the returned `Vec`.
    /// If you want to just use a default state value, use [`Parser::check`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[T]`], a [`&str`], [`Stream`], or anything implementing [`Input`] to it.
    fn check_with_state(&self, input: I, state: &mut E::State) -> ParseResult<(), E::Error>
    where
        Self: Sized,
        I: Input<'a>,
        E::Context: Default,
    {
        let ctx = E::Context::default();
        let mut inp = InputRef::new(&input, state, &ctx);
        let res = self.go::<Check>(&mut inp);
        let res = res.and_then(|()| expect_end(&mut inp));
        let alt = inp.errors.alt.take();
        let mut errs = inp.into_errs();
        let out = match res {
            Ok(()) => Some(()),
            Err(()) => {
                errs.push(alt.expect("error but no alt?").err);
                None
            }
        };
        ParseResult::new(out, errs)
    }

    /// Parse a stream with all the bells & whistles. You can use this to implement your own parser combinators. Note
    /// that both the signature and semantic requirements of this function are very likely to change in later versions.
    /// Where possible, prefer more ergonomic combinators provided elsewhere in the crate rather than implementing your
    /// own.
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized;

    #[doc(hidden)]
    fn go_emit(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Emit, O>;
    #[doc(hidden)]
    fn go_check(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Check, O>;

    /// Map from a slice of the input based on the current parser's span to a value.
    ///
    /// The returned value may borrow data from the input slice, making this function very useful
    /// for creating zero-copy AST output values
    fn map_slice<U, F: Fn(I::Slice) -> U>(self, f: F) -> MapSlice<'a, Self, I, O, E, F, U>
    where
        Self: Sized,
        I: SliceInput<'a>,
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
    fn slice(self) -> Slice<Self, O>
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let lowercase = any::<_, extra::Err<Simple<char>>>()
    ///     .filter(char::is_ascii_lowercase)
    ///     .repeated()
    ///     .at_least(1)
    ///     .collect::<String>();
    ///
    /// assert_eq!(lowercase.parse("hello").into_result(), Ok("hello".to_string()));
    /// assert!(lowercase.parse("Hello").has_errors());
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// #[derive(Debug, PartialEq)]
    /// enum Token { Word(String), Num(u64) }
    ///
    /// let word = any::<_, extra::Err<Simple<char>>>()
    ///     .filter(|c: &char| c.is_alphabetic())
    ///     .repeated().at_least(1)
    ///     .collect::<String>()
    ///     .map(Token::Word);
    ///
    /// let num = any::<_, extra::Err<Simple<char>>>()
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
    /// pub struct Spanned<T>(T, SimpleSpan<usize>);
    ///
    /// let ident = text::ident::<_, _, extra::Err<Simple<char>>>()
    ///     .map_with_span(|ident, span| Spanned(ident, span))
    ///     .padded();
    ///
    /// assert_eq!(ident.parse("hello").into_result(), Ok(Spanned("hello", (0..5).into())));
    /// assert_eq!(ident.parse("       hello   ").into_result(), Ok(Spanned("hello", (7..12).into())));
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
    /// pub struct Spanned<T>(T, SimpleSpan<usize>);
    ///
    /// let ident = text::ident::<_, _, extra::Err<Simple<char>>>()
    ///     .map_with_span(|ident, span| Spanned(ident, span))
    ///     .padded();
    ///
    /// assert_eq!(ident.parse("hello").into_result(), Ok(Spanned("hello", (0..5).into())));
    /// assert_eq!(ident.parse("       hello   ").into_result(), Ok(Spanned("hello", (7..12).into())));
    /// ```
    fn map_with_state<U, F: Fn(O, I::Span, &mut E::State) -> U>(
        self,
        f: F,
    ) -> MapWithState<Self, O, F>
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
    /// let byte = text::int::<_, _, extra::Err<Rich<char>>>(10)
    ///     .try_map(|s: &str, span| s
    ///         .parse::<u8>()
    ///         .map_err(|e| Rich::custom(span, e)));
    ///
    /// assert!(byte.parse("255").has_output());
    /// assert!(byte.parse("256").has_errors()); // Out of range
    /// ```
    #[doc(alias = "filter_map")]
    fn try_map<U, F: Fn(O, I::Span) -> Result<U, E::Error>>(self, f: F) -> TryMap<Self, O, F>
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
    fn try_map_with_state<U, F: Fn(O, I::Span, &mut E::State) -> Result<U, E::Error>>(
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// // A parser that parses any number of whitespace characters without allocating
    /// let whitespace = any::<_, extra::Err<Simple<char>>>()
    ///     .filter(|c: &char| c.is_whitespace())
    ///     .ignored()
    ///     .repeated()
    ///     .collect::<Vec<_>>();
    ///
    /// assert_eq!(whitespace.parse("    ").into_result(), Ok(vec![(); 4]));
    /// assert!(whitespace.parse("  hello").has_errors());
    /// ```
    fn ignored(self) -> Ignored<Self, O>
    where
        Self: Sized,
    {
        Ignored {
            parser: self,
            phantom: PhantomData,
        }
    }

    /// Memoise the parser such that later attempts to parse the same input 'remember' the attempt and exit early.
    ///
    /// If you're finding that certain inputs produce exponential behaviour in your parser, strategically applying
    /// memoisation to a ['garden path'](https://en.wikipedia.org/wiki/Garden-path_sentence) rule is often an effective
    /// way to solve the problem. At the limit, applying memoisation to all combinators will turn any parser into one
    /// with `O(n)`, albeit with very significant per-element overhead and high memory usage.
    ///
    /// Memoisation also works with recursion, so this can be used to write parsers using
    /// [left recursion](https://en.wikipedia.org/wiki/Left_recursion).
    // TODO: Example
    #[cfg(feature = "memoization")]
    fn memoised(self) -> Memoised<Self>
    where
        Self: Sized,
    {
        Memoised { parser: self }
    }

    /// Transform all outputs of this parser to a pretermined value.
    ///
    /// The output type of this parser is `U`, the type of the predetermined value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Simple};
    /// #[derive(Clone, Debug, PartialEq)]
    /// enum Op { Add, Sub, Mul, Div }
    ///
    /// let op = just::<_, _, extra::Err<Simple<char>>>('+').to(Op::Add)
    ///     .or(just('-').to(Op::Sub))
    ///     .or(just('*').to(Op::Mul))
    ///     .or(just('/').to(Op::Div));
    ///
    /// assert_eq!(op.parse("+").into_result(), Ok(Op::Add));
    /// assert_eq!(op.parse("/").into_result(), Ok(Op::Div));
    /// ```
    fn to<U: Clone>(self, to: U) -> To<Self, O, U, E>
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let word = any::<_, extra::Err<Simple<char>>>()
    ///     .filter(|c: &char| c.is_alphabetic())
    ///     .repeated()
    ///     .at_least(1)
    ///     .collect::<String>();
    /// let two_words = word.then_ignore(just(' ')).then(word);
    ///
    /// assert_eq!(two_words.parse("dog cat").into_result(), Ok(("dog".to_string(), "cat".to_string())));
    /// assert!(two_words.parse("hedgehog").has_errors());
    /// ```
    fn then<U, B: Parser<'a, I, U, E>>(self, other: B) -> Then<Self, B, O, U, E>
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let zeroes = any::<_, extra::Err<Simple<char>>>().filter(|c: &char| *c == '0').ignored().repeated().collect::<Vec<_>>();
    /// let digits = any().filter(|c: &char| c.is_ascii_digit())
    ///     .repeated()
    ///     .collect::<String>();
    /// let integer = zeroes
    ///     .ignore_then(digits)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// assert_eq!(integer.parse("00064").into_result(), Ok(64));
    /// assert_eq!(integer.parse("32").into_result(), Ok(32));
    /// ```
    fn ignore_then<U, B: Parser<'a, I, U, E>>(self, other: B) -> IgnoreThen<Self, B, O, E>
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let word = any::<_, extra::Err<Simple<char>>>()
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
    fn then_ignore<U, B: Parser<'a, I, U, E>>(self, other: B) -> ThenIgnore<Self, B, U, E>
    where
        Self: Sized,
    {
        ThenIgnore {
            parser_a: self,
            parser_b: other,
            phantom: PhantomData,
        }
    }

    /// TODO
    fn nested_in<B: Parser<'a, I, I, E>>(self, other: B) -> NestedIn<Self, B, O, E>
    where
        Self: Sized,
        I: 'a,
    {
        NestedIn {
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let successor = just(b'\0').configure(|cfg, ctx: &u8| cfg.seq(*ctx + 1));
    ///
    /// // A parser that parses a single letter and then its successor
    /// let successive_letters = one_of::<_, _, extra::Err<Simple<u8>>>(b'a'..=b'z')
    ///     .then_with_ctx(successor);
    ///
    /// assert_eq!(successive_letters.parse(b"ab").into_result(), Ok(b'b')); // 'b' follows 'a'
    /// assert!(successive_letters.parse(b"ac").has_errors()); // 'c' does not follow 'a'
    /// ```
    fn then_with_ctx<U, P>(
        self,
        then: P,
    ) -> ThenWithCtx<Self, P, O, I, extra::Full<E::Error, E::State, O>>
    where
        Self: Sized,
        O: 'a,
        P: Parser<'a, I, U, extra::Full<E::Error, E::State, O>>,
    {
        ThenWithCtx {
            parser: self,
            then,
            phantom: PhantomData,
        }
    }

    /// Run the previous contextual parser with the provided context
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// # use chumsky::primitive::JustCfg;
    ///
    /// let generic = just(b'0').configure(|cfg, ctx: &u8| cfg.seq(*ctx));
    ///
    /// let parse_a = just::<_, _, extra::Default>(b'b').ignore_then(generic.with_ctx::<u8>(b'a'));
    /// let parse_b = just::<_, _, extra::Default>(b'a').ignore_then(generic.with_ctx(b'b'));
    ///
    /// assert_eq!(parse_a.parse(b"ba" as &[_]).into_result(), Ok::<_, Vec<EmptyErr>>(b'a'));
    /// assert!(parse_a.parse(b"bb").has_errors());
    /// assert_eq!(parse_b.parse(b"ab" as &[_]).into_result(), Ok(b'b'));
    /// assert!(parse_b.parse(b"aa").has_errors());
    /// ```
    fn with_ctx<Ctx>(self, ctx: Ctx) -> WithCtx<Self, Ctx>
    where
        Self: Sized,
        Ctx: 'a + Clone,
    {
        WithCtx { parser: self, ctx }
    }

    /// ```
    /// # use chumsky::{prelude::*, error::Simple};
    ///
    /// let escape = just("\\n").to('\n');
    ///
    /// // C-style tring literal
    /// let string = none_of::<_, _, extra::Err<Simple<char>>>('"')
    ///     .and_is(escape.not())
    ///     .or(escape)
    ///     .repeated()
    ///     .collect::<String>()
    ///     .padded_by(just('"'));
    ///
    /// assert_eq!(
    ///     string.parse("\"wxyz\"").into_result().as_deref(),
    ///     Ok("wxyz"),
    /// );
    /// assert_eq!(
    ///     string.parse("\"a\nb\"").into_result().as_deref(),
    ///     Ok("a\nb"),
    /// );
    /// ```
    fn and_is<U, B>(self, other: B) -> AndIs<Self, B, U>
    where
        Self: Sized,
        B: Parser<'a, I, U, E>,
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// // A LISP-style S-expression
    /// #[derive(Debug, PartialEq)]
    /// enum SExpr {
    ///     Ident(String),
    ///     Num(u64),
    ///     List(Vec<SExpr>),
    /// }
    ///
    /// let ident = any::<_, extra::Err<Simple<char>>>().filter(|c: &char| c.is_alphabetic())
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
        B: Parser<'a, I, U, E>,
        C: Parser<'a, I, V, E>,
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let ident = text::ident::<_, _, extra::Err<Simple<char>>>()
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
        B: Parser<'a, I, U, E>,
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let op = just::<_, _, extra::Err<Simple<char>>>('+')
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
        B: Parser<'a, I, O, E>,
    {
        Or {
            choice: choice((self, other)),
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let word = any::<_, extra::Err<Simple<char>>>().filter(|c: &char| c.is_alphabetic())
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
    /// # use chumsky::{prelude::*, error::Simple};
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Tree<'a> {
    ///     Text(&'a str),
    ///     Group(Vec<Self>),
    /// }
    ///
    /// // Arbitrary text, nested in a tree with { ... } delimiters
    /// let tree = recursive::<_, _, extra::Err<Simple<char>>, _, _>(|tree| {
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let num = any::<_, extra::Err<Simple<char>>>()
    ///     .filter(|c: &char| c.is_ascii_digit())
    ///     .repeated()
    ///     .at_least(1)
    ///     .collect::<String>()
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let sum = num.clone()
    ///     .foldl(just('+').ignore_then(num).repeated(), |a, b| a + b);
    ///
    /// assert_eq!(sum.parse("2+13+4+0+5").into_result(), Ok(24));
    /// ```
    fn repeated(self) -> Repeated<Self, O, I, E>
    where
        Self: Sized,
    {
        Repeated {
            parser: self,
            at_least: 0,
            at_most: !0,
            phantom: PhantomData,
        }
    }

    /// Parse a pattern a specific number of times.
    ///
    /// Input is eagerly parsed. Consider using [`RepeatedExactly::repeated`] if a non-constant number of values are expected.
    ///
    /// The output type of this parser can be any [`ContainerExactly`].
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let shopping = text::ident::<_, _, extra::Err<Simple<char>>>()
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .collect::<Vec<_>>();
    ///
    /// assert_eq!(shopping.parse("eggs").into_result(), Ok(vec!["eggs"]));
    /// assert_eq!(shopping.parse("eggs, flour, milk").into_result(), Ok(vec!["eggs", "flour", "milk"]));
    /// ```
    ///
    /// See [`SeparatedBy::allow_leading`] and [`SeparatedBy::allow_trailing`] for more examples.
    fn separated_by<U, B>(self, separator: B) -> SeparatedBy<Self, B, O, U, I, E>
    where
        Self: Sized,
        B: Parser<'a, I, U, E>,
    {
        SeparatedBy {
            parser: self,
            separator,
            at_least: 0,
            at_most: !0,
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
        B: Parser<'a, I, U, E>,
    {
        SeparatedByExactly {
            parser: self,
            separator,
            allow_leading: false,
            allow_trailing: false,
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let int = text::int::<_, _, extra::Err<Simple<char>>>(10)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let sum = int
    ///     .clone()
    ///     .foldl(just('+').ignore_then(int).repeated(), |a, b| a + b);
    ///
    /// assert_eq!(sum.parse("1+12+3+9").into_result(), Ok(25));
    /// assert_eq!(sum.parse("6").into_result(), Ok(6));
    /// ```
    fn foldl<B, F, OB>(self, other: B, f: F) -> Foldl<F, Self, B, OB, E>
    where
        F: Fn(O, OB) -> O,
        B: IterParser<'a, I, OB, E>,
        Self: Sized,
    {
        Foldl {
            parser_a: self,
            parser_b: other,
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
    /// let just_numbers = text::digits::<_, _, extra::Err<Simple<char>>>(10)
    ///     .slice()
    ///     .padded()
    ///     .then_ignore(none_of("+-*/").rewind())
    ///     .separated_by(just(','))
    ///     .collect::<Vec<_>>();
    /// // 3 is not parsed because it's followed by '+'.
    /// assert_eq!(just_numbers.lazy().parse("1, 2, 3 + 4").into_result(), Ok(vec!["1", "2"]));
    /// ```
    fn rewind(self) -> Rewind<Self>
    where
        Self: Sized,
    {
        Rewind { parser: self }
    }

    /// Make the parser lazy, such that it parses as much as it validly can and then finished successfully, leaving
    /// trailing input untouched.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let digits = one_of::<_, _, extra::Err<Simple<char>>>('0'..='9')
    ///     .repeated()
    ///     .collect::<String>()
    ///     .lazy();
    ///
    /// assert_eq!(digits.parse("12345abcde").into_result().as_deref(), Ok("12345"));
    /// ```
    fn lazy(self) -> Lazy<'a, Self, I, E>
    where
        Self: Sized,
        I: ValueInput<'a>,
    {
        self.then_ignore(any().repeated())
    }

    /// Parse a pattern, ignoring any amount of whitespace both before and after the pattern.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let ident = text::ident::<_, _, extra::Err<Simple<char>>>().padded();
    ///
    /// // A pattern with no whitespace surrounding it is accepted
    /// assert_eq!(ident.parse("hello").into_result(), Ok("hello"));
    /// // A pattern with arbitrary whitespace surrounding it is also accepted
    /// assert_eq!(ident.parse(" \t \n  \t   world  \t  ").into_result(), Ok("world"));
    /// ```
    fn padded(self) -> Padded<Self>
    where
        Self: Sized,
        I: Input<'a>,
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// #[derive(Debug, PartialEq)]
    /// enum Expr<'a> {
    ///     Error,
    ///     Int(&'a str),
    ///     List(Vec<Expr<'a>>),
    /// }
    ///
    /// let recovery = just::<_, _, extra::Err<Simple<char>>>('[')
    ///         .then(none_of(']').repeated().then(just(']')));
    ///
    /// let expr = recursive::<_, _, extra::Err<Simple<char>>, _, _>(|expr| expr
    ///     .separated_by(just(','))
    ///     .collect::<Vec<_>>()
    ///     .delimited_by(just('['), just(']'))
    ///     .map(Expr::List)
    ///     // If parsing a list expression fails, recover at the next delimiter, generating an error AST node
    ///     .recover_with(via_parser(recovery.map(|_| Expr::Error)))
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
    fn recover_with<S: Strategy<'a, I, O, E>>(self, strategy: S) -> RecoverWith<Self, S>
    where
        Self: Sized,
    {
        RecoverWith {
            parser: self,
            strategy,
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
        F: Fn(E::Error) -> E::Error,
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
        F: Fn(E::Error, I::Span) -> E::Error,
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
        F: Fn(E::Error, I::Span, &mut E::State) -> E::Error,
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
    /// # use chumsky::prelude::*;
    /// let large_int = text::int::<_, _, extra::Err<Rich<char>>>(10)
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
    fn validate<U, F>(self, f: F) -> Validate<Self, O, F>
    where
        Self: Sized,
        F: Fn(O, I::Span, &mut Emitter<E::Error>) -> U,
    {
        Validate {
            parser: self,
            validator: f,
            phantom: PhantomData,
        }
    }

    /// Map the primary error of this parser to a result. If the result is [`Ok`], the parser succeeds with that value.
    ///
    /// Note that, if the closure returns [`Err`], the parser will not consume any input.
    ///
    /// The output type of this parser is `U`, the [`Ok`] type of the result.
    fn or_else<F>(self, f: F) -> OrElse<Self, F>
    where
        Self: Sized,
        F: Fn(E::Error) -> Result<O, E::Error>,
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
    /// let uint64 = text::int::<_, _, extra::Err<Simple<char>>>(10)
    ///     .from_str::<u64>()
    ///     .unwrapped();
    ///
    /// assert_eq!(uint64.parse("7").into_result(), Ok(7));
    /// assert_eq!(uint64.parse("42").into_result(), Ok(42));
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
    /// let boolean = just::<_, _, extra::Err<Simple<char>>>("true")
    ///     .or(just("false"))
    ///     .from_str::<bool>()
    ///     .unwrapped(); // Cannot panic: the only possible outputs generated by the parser are "true" or "false"
    ///
    /// assert_eq!(boolean.parse("true").into_result(), Ok(true));
    /// assert_eq!(boolean.parse("false").into_result(), Ok(false));
    /// // Does not panic, because the original parser only accepts "true" or "false"
    /// assert!(boolean.parse("42").has_errors());
    /// ```
    // TODO: Use Location::caller(), make this a proper combinator
    #[track_caller]
    fn unwrapped(self) -> Unwrapped<Self, O>
    where
        Self: Sized,
    {
        Unwrapped {
            parser: self,
            location: *Location::caller(),
            phantom: PhantomData,
        }
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
    fn boxed(self) -> Boxed<'a, I, O, E>
    where
        Self: Sized + 'a,
    {
        Boxed {
            inner: Rc::new(self),
        }
    }
}

#[cfg(feature = "nightly")]
impl<'a, I, O, E> Parser<'a, I, O, E> for !
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    fn go<M: Mode>(&self, _inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        *self
    }

    go_extra!(O);
}

/// A parser that can be configured with runtime context
pub trait ConfigParser<'a, I, O, E>: Parser<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    /// Type used to configure the parser
    type Config: Default;

    /// Parse a stream with the provided configured values. This can be used to control a parser's
    /// behavior at parse-time.
    fn go_cfg<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>, cfg: Self::Config) -> PResult<M, O>
    where
        Self: Sized;

    #[doc(hidden)]
    fn go_emit_cfg(&self, inp: &mut InputRef<'a, '_, I, E>, cfg: Self::Config) -> PResult<Emit, O>;
    #[doc(hidden)]
    fn go_check_cfg(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        cfg: Self::Config,
    ) -> PResult<Check, O>;

    /// A combinator that allows configuration of the parser from the current context
    fn configure<F>(self, cfg: F) -> Configure<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Config, &E::Context) -> Self::Config,
    {
        Configure { parser: self, cfg }
    }
}

/// An iterator that wraps an iterable parser. See [`IterParser::parse_iter`].
pub struct ParserIter<'a, 'iter, P: IterParser<'a, I, O, E>, I: Input<'a>, O, E: ParserExtra<'a, I>>
{
    parser: P,
    input: I,
    offset: I::Offset,
    state: MaybeMut<'iter, E::State>,
    errors: input::Errors<E::Error>,
    ctx: E::Context,
    #[cfg(feature = "memoization")]
    memos: HashMap<(I::Offset, usize), Option<Located<E::Error>>>,
    iter_state: Option<P::IterState<Emit>>,
    phantom: PhantomData<&'a O>,
}

impl<'a, 'iter, P, I: Input<'a>, O, E: ParserExtra<'a, I>> Iterator
    for ParserIter<'a, 'iter, P, I, O, E>
where
    P: IterParser<'a, I, O, E>,
{
    type Item = O;

    fn next(&mut self) -> Option<Self::Item> {
        let mut inp = InputRef {
            input: &self.input,
            offset: self.offset,
            errors: core::mem::take(&mut self.errors),
            state: &mut *self.state,
            ctx: &self.ctx,
            // TODO: Work out how to note take, since this probably allocates in `HashMap::default`
            #[cfg(feature = "memoization")]
            memos: core::mem::take(&mut self.memos),
        };
        let parser = &self.parser;

        let iter_state = match &mut self.iter_state {
            Some(state) => state,
            None => {
                let state = parser.make_iter::<Emit>(&mut inp).ok()?;
                self.iter_state = Some(state);
                self.iter_state.as_mut().unwrap()
            }
        };

        let res = parser.next::<Emit>(&mut inp, iter_state);
        self.offset = inp.offset;
        self.errors = inp.errors;
        #[cfg(feature = "memoization")]
        {
            self.memos = inp.memos;
        }
        res.ok().and_then(|res| res)
    }
}

/// An iterable equivalent of [`Parser`], i.e: a parser that generates a sequence of outputs.
// TODO: Make sealed
pub trait IterParser<'a, I: Input<'a>, O, E: ParserExtra<'a, I> = extra::Default> {
    /// The state of the iterator during iteration.
    type IterState<M: Mode>
    where
        I: 'a;

    #[doc(hidden)]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>>;
    #[doc(hidden)]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, O>;

    /// Collect this iterable parser into a [`Container`].
    ///
    /// This is commonly useful for collecting parsers that many values outputs into containers of various kinds:
    /// [`Vec`]s, [`String`]s, or even [`HashMap`]s. This method is analogous to [`Iterator::collect`].
    ///
    /// The output type of this parser is `C`, the type being collected into.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Simple};
    /// let word = any::<_, extra::Err<Simple<char>>>().filter(|c: &char| c.is_alphabetic()) // This parser produces an output of `char`
    ///     .repeated() // This parser is iterable (i.e: implements `IterParser`)
    ///     .collect::<String>(); // We collect the `char`s into a `String`
    ///
    /// assert_eq!(word.parse("hello").into_result(), Ok("hello".to_string()));
    /// ```
    fn collect<C: Container<O>>(self) -> Collect<Self, O, C>
    where
        Self: Sized,
    {
        Collect {
            parser: self,
            phantom: PhantomData,
        }
    }

    /// Collect this iterable parser into a [`usize`], outputting the number of elements that were parsed.
    ///
    /// This is sugar for [`.collect::<usize>()`](Self::collect).
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    ///
    /// // Counts how many chess squares are in the input.
    /// let squares = one_of::<_, _, extra::Err<Simple<char>>>('a'..='z').then(one_of('1'..='8')).padded().repeated().count();
    ///
    /// assert_eq!(squares.parse("a1 b2 c3").into_result(), Ok(3));
    /// assert_eq!(squares.parse("e5 e7 c6 c7 f6 d5 e6 d7 e4 c5 d6 c4 b6 f5").into_result(), Ok(14));
    /// assert_eq!(squares.parse("").into_result(), Ok(0));
    /// ```
    fn count(self) -> Collect<Self, O, usize>
    where
        Self: Sized,
    {
        self.collect()
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
    /// # use chumsky::{prelude::*, error::Simple};
    /// let int = text::int::<_, _, extra::Err<Simple<char>>>(10)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let signed = just('+').to(1)
    ///     .or(just('-').to(-1))
    ///     .repeated()
    ///     .foldr(int, |a, b| a * b);
    ///
    /// assert_eq!(signed.parse("3").into_result(), Ok(3));
    /// assert_eq!(signed.parse("-17").into_result(), Ok(-17));
    /// assert_eq!(signed.parse("--+-+-5").into_result(), Ok(5));
    /// ```
    fn foldr<B, F, OA>(self, other: B, f: F) -> Foldr<F, Self, B, O, E>
    where
        F: Fn(O, OA) -> OA,
        B: Parser<'a, I, OA, E>,
        Self: Sized,
    {
        Foldr {
            parser_a: self,
            parser_b: other,
            folder: f,
            phantom: PhantomData,
        }
    }

    /// Create an iterator over the outputs generated by an iterable parser.
    ///
    /// Warning: Trailing errors will be ignored
    fn parse_iter(self, input: I) -> ParseResult<ParserIter<'a, 'static, Self, I, O, E>, E::Error>
    where
        Self: IterParser<'a, I, O, E> + Sized,
        E::State: Default,
        E::Context: Default,
    {
        ParseResult::new(
            Some(ParserIter {
                parser: self,
                offset: input.start(),
                input,
                state: MaybeMut::new_own(E::State::default()),
                ctx: E::Context::default(),
                errors: input::Errors::default(),
                #[cfg(feature = "memoization")]
                memos: HashMap::default(),
                iter_state: None,
                phantom: PhantomData,
            }),
            Vec::new(),
        )
    }

    /// Create an iterator over the outputs generated by an iterable parser with the given parser state.
    ///
    /// Warning: Trailing errors will be ignored
    fn parse_iter_with_state<'parse>(
        self,
        input: I,
        state: &'parse mut E::State,
    ) -> ParseResult<ParserIter<'a, 'parse, Self, I, O, E>, E::Error>
    where
        Self: IterParser<'a, I, O, E> + Sized,
        E::Context: Default,
    {
        ParseResult::new(
            Some(ParserIter {
                parser: self,
                offset: input.start(),
                input,
                state: MaybeMut::new_ref(state),
                ctx: E::Context::default(),
                errors: input::Errors::default(),
                #[cfg(feature = "memoization")]
                memos: HashMap::default(),
                iter_state: None,
                phantom: PhantomData,
            }),
            Vec::new(),
        )
    }
}

/// An iterable equivalent of [`ConfigParser`], i.e: a parser that generates a sequence of outputs and
/// can be configured at runtime.
pub trait ConfigIterParser<'a, I: Input<'a>, O, E: ParserExtra<'a, I> = extra::Default>:
    IterParser<'a, I, O, E>
{
    /// Type used to configure the parser
    type Config: Default;

    #[doc(hidden)]
    fn next_cfg<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
        cfg: &Self::Config,
    ) -> IPResult<M, O>;

    /// A combinator that allows configuration of the parser from the current context
    fn configure<F>(self, cfg: F) -> IterConfigure<Self, F, O>
    where
        Self: Sized,
        F: Fn(Self::Config, &E::Context) -> Self::Config,
    {
        IterConfigure {
            parser: self,
            cfg,
            phantom: PhantomData,
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
pub struct Boxed<'a, I: Input<'a>, O, E: ParserExtra<'a, I>> {
    inner: Rc<dyn Parser<'a, I, O, E> + 'a>,
}

impl<'a, I: Input<'a>, O, E: ParserExtra<'a, I>> Clone for Boxed<'a, I, O, E> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, I, O, E> Parser<'a, I, O, E> for Boxed<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        M::invoke(&*self.inner, inp)
    }

    fn boxed(self) -> Boxed<'a, I, O, E>
    where
        Self: Sized + 'a,
    {
        // Never double-box parsers
        self
    }

    go_extra!(O);
}

/// Create a parser that selects one or more input patterns and map them to an output value.
///
/// This is most useful when turning the tokens of a previous compilation pass (such as lexing) into data that can be
/// used for parsing, although it can also generally be used to select inputs and map them to outputs. Any unmapped
/// input patterns will become syntax errors, just as with [`Parser::filter`].
///
/// Internally, [`select!`] is very similar to [`Parser::try_map`] and thinking of it as such might make it less
/// confusing.
///
/// `select!` requires that tokens implement [`Clone`].
///
/// If you're trying to access tokens referentially (for the sake of nested parsing, or simply because you want to
/// avoid cloning the token), see [`select_ref!`].
///
/// # Examples
///
/// `select!` is syntactically similar to a `match` expression and has support for
/// [pattern guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards):
///
/// ```
/// # use chumsky::{prelude::*, error::Simple};
/// #[derive(Clone)]
/// enum Token<'a> { Ident(&'a str) }
///
/// enum Expr<'a> { Local(&'a str), Null, True, False }
///
/// # let _: chumsky::primitive::Select<_, &[Token], Expr, extra::Default> =
/// select! {
///     Token::Ident(s) if s == "true" => Expr::True,
///     Token::Ident(s) if s == "false" => Expr::False,
///     Token::Ident(s) if s == "null" => Expr::Null,
///     Token::Ident(s) => Expr::Local(s),
/// }
/// # ;
/// ```
///
/// If you require access to the token's span, you may add an argument after a pattern to gain access to it:
///
/// ```
/// # use chumsky::{prelude::*, error::Simple};
/// #[derive(Clone)]
/// enum Token<'a> { Num(f64), Str(&'a str) }
///
/// enum Expr<'a> { Num(f64), Str(&'a str) }
///
/// type Span = SimpleSpan<usize>;
///
/// impl<'a> Expr<'a> {
///     fn spanned(self, span: Span) -> (Self, Span) { (self, span) }
/// }
///
/// # let _: chumsky::primitive::Select<_, &[Token], (Expr, Span), extra::Default> =
/// select! {
///     Token::Num(x) = span => Expr::Num(x).spanned(span),
///     Token::Str(s) = span => Expr::Str(s).spanned(span),
/// }
/// # ;
/// ```
///
/// ```
/// # use chumsky::{prelude::*, error::Simple};
/// // The type of our parser's input (tokens like this might be emitted by your compiler's lexer)
/// #[derive(Clone, Debug, PartialEq)]
/// enum Token {
///     Num(u64),
///     Bool(bool),
///     LParen,
///     RParen,
/// }
///
/// // The type of our parser's output, a syntax tree
/// #[derive(Debug, PartialEq)]
/// enum Ast {
///     Num(u64),
///     Bool(bool),
///     List(Vec<Ast>),
/// }
///
/// // Our parser converts a stream of input tokens into an AST
/// // `select!` is used to deconstruct some of the tokens and turn them into AST nodes
/// let ast = recursive::<_, _, extra::Err<Simple<Token>>, _, _>(|ast| {
///     let literal = select! {
///         Token::Num(x) => Ast::Num(x),
///         Token::Bool(x) => Ast::Bool(x),
///     };
///
///     literal.or(ast
///         .repeated()
///         .collect()
///         .delimited_by(just(Token::LParen), just(Token::RParen))
///         .map(Ast::List))
/// });
///
/// use Token::*;
/// assert_eq!(
///     ast.parse(&[LParen, Num(5), LParen, Bool(false), Num(42), RParen, RParen]).into_result(),
///     Ok(Ast::List(vec![
///         Ast::Num(5),
///         Ast::List(vec![
///             Ast::Bool(false),
///             Ast::Num(42),
///         ]),
///     ])),
/// );
/// ```
#[macro_export]
macro_rules! select {
    ($($p:pat $(= $span:ident)? $(if $guard:expr)? $(=> $out:expr)?),+ $(,)?) => ({
        $crate::primitive::select(
            move |x, span| match x {
                $($p $(if $guard)? => ::core::option::Option::Some({ $(let $span = span;)? () $(;$out)? })),+,
                _ => ::core::option::Option::None,
            }
        )
    });
}

/// A version of [`select!`] that selects on token by reference instead of by value.
///
/// Useful if you want to extract elements from a token in a zero-copy manner.
///
/// `select_ref` requires that the parser input implements [`BorrowInput`].
// TODO: Remove this, somehow unify with `select`?
#[macro_export]
macro_rules! select_ref {
    ($($p:pat $(= $span:ident)? $(if $guard:expr)? $(=> $out:expr)?),+ $(,)?) => ({
        $crate::primitive::select_ref(
            move |x, span| match x {
                $($p $(if $guard)? => ::core::option::Option::Some({ $(let $span = span;)? () $(;$out)? })),+,
                _ => ::core::option::Option::None,
            }
        )
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_copy() {
        use self::input::WithContext;
        use self::prelude::*;

        #[derive(PartialEq, Debug)]
        enum Token<'a> {
            Ident(&'a str),
            String(&'a str),
        }

        type FileId = u32;

        type Span = (FileId, SimpleSpan<usize>);

        fn parser<'a>() -> impl Parser<'a, WithContext<FileId, &'a str>, [(Span, Token<'a>); 6]> {
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
            parser()
                .parse(r#"hello "world" these are "test" tokens"#.with_context(42))
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

    #[test]
    fn zero_copy_repetition() {
        use self::prelude::*;

        fn parser<'a>() -> impl Parser<'a, &'a str, Vec<u64>> {
            any()
                .filter(|c: &char| c.is_ascii_digit())
                .repeated()
                .at_least(1)
                .at_most(3)
                .map_slice(|b: &str| b.parse::<u64>().unwrap())
                .padded()
                .separated_by(just(',').padded())
                .allow_trailing()
                .collect()
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

        fn parser<'a>() -> impl Parser<'a, &'a str, (&'a str, u64, char)> {
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

    #[test]
    fn zero_copy_group_array() {
        use self::prelude::*;

        fn parser<'a>() -> impl Parser<'a, &'a str, [char; 3]> {
            group([just('a'), just('b'), just('c')])
        }

        assert_eq!(parser().parse("abc").into_result(), Ok(['a', 'b', 'c']));
        assert!(parser().parse("abd").has_errors());
    }

    #[test]
    fn unicode_str() {
        let input = "🄯🄚🹠🴎🄐🝋🰏🄂🬯🈦g🸵🍩🕔🈳2🬙🨞🅢🭳🎅h🵚🧿🏩🰬k🠡🀔🈆🝹🤟🉗🴟📵🰄🤿🝜🙘🹄5🠻🡉🱖🠓";
        let mut state = ();
        let ctx = ();
        let mut input = InputRef::<_, extra::Default>::new(&input, &mut state, &ctx);

        while let (_, Some(c)) = input.next() {
            std::hint::black_box(c);
        }
    }

    #[test]
    fn iter() {
        use self::prelude::*;

        fn parser<'a>() -> impl IterParser<'a, &'a str, char> {
            any().repeated()
        }

        let mut chars = String::new();
        for c in parser().parse_iter(&"abcdefg").into_result().unwrap() {
            chars.push(c);
        }

        assert_eq!(&chars, "abcdefg");
    }

    #[test]
    #[cfg(feature = "memoization")]
    fn exponential() {
        use self::prelude::*;

        fn parser<'a>() -> impl Parser<'a, &'a str, String> {
            recursive(|expr| {
                let atom = any()
                    .filter(|c: &char| c.is_alphabetic())
                    .repeated()
                    .at_least(1)
                    .collect()
                    .or(expr.delimited_by(just('('), just(')')));

                atom.clone()
                    .then_ignore(just('+'))
                    .then(atom.clone())
                    .map(|(a, b)| format!("{}{}", a, b))
                    .memoised()
                    .or(atom)
            })
            .then_ignore(end())
        }

        parser()
            .parse("((((((((((((((((((((((((((((((a+b))))))))))))))))))))))))))))))")
            .into_result()
            .unwrap();
    }

    #[test]
    #[cfg(feature = "memoization")]
    fn left_recursive() {
        use self::prelude::*;

        fn parser<'a>() -> impl Parser<'a, &'a str, String> {
            recursive(|expr| {
                let atom = any()
                    .filter(|c: &char| c.is_alphabetic())
                    .repeated()
                    .at_least(1)
                    .collect();

                let sum = expr
                    .clone()
                    .then_ignore(just('+'))
                    .then(expr)
                    .map(|(a, b)| format!("{}{}", a, b))
                    .memoised();

                sum.or(atom)
            })
            .then_ignore(end())
        }

        assert_eq!(parser().parse("a+b+c").into_result().unwrap(), "abc");
    }
}
