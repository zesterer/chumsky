#![cfg_attr(not(any(doc, feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_auto_cfg, doc_cfg), deny(rustdoc::all))]
#![cfg_attr(feature = "nightly", allow(internal_features))]
#![cfg_attr(
    feature = "nightly",
    feature(
        never_type,
        fn_traits,
        tuple_trait,
        unboxed_closures,
        diagnostic_namespace
    )
)]
//
// README.md links these files via the main branch. For docs.rs we however want to link them
// to the version of the documented crate since the files in the main branch may diverge.
#![doc = concat!("[`examples/brainfuck.rs`]: ", blob_url_prefix!(), "/examples/brainfuck.rs")]
#![doc = concat!("[JSON parser]: ", blob_url_prefix!(), "/examples/json.rs")]
#![doc = concat!("[examples/nano_rust.rs]: ", blob_url_prefix!(), "/examples/nano_rust.rs")]
#![doc = concat!("[tutorial]: ", blob_url_prefix!(), "/tutorial.md")]
//
#![doc = include_str!("../README.md")]
#![deny(missing_docs, clippy::undocumented_unsafe_blocks)]
#![allow(
    clippy::should_implement_trait,
    clippy::type_complexity,
    clippy::result_unit_err
)]
// TODO: Talk about `.map` and purity assumptions

extern crate alloc;
extern crate core;

#[cfg(feature = "docsrs")]
macro_rules! blob_url_prefix {
    () => {
        concat!(
            "https://github.com/zesterer/chumsky/blob/",
            env!("VERGEN_GIT_SHA")
        )
    };
}

#[cfg(not(feature = "docsrs"))]
macro_rules! blob_url_prefix {
    () => {
        concat!(
            "https://github.com/zesterer/chumsky/blob/",
            env!("CARGO_PKG_VERSION")
        )
    };
}

macro_rules! go_extra {
    ( $O :ty ) => {
        #[inline(always)]
        fn go_emit(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Emit, $O> {
            ParserSealed::<I, $O, E>::go::<Emit>(self, inp)
        }
        #[inline(always)]
        fn go_check(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Check, $O> {
            ParserSealed::<I, $O, E>::go::<Check>(self, inp)
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
            ConfigParserSealed::<I, $O, E>::go_cfg::<Emit>(self, inp, cfg)
        }
        #[inline(always)]
        fn go_check_cfg(
            &self,
            inp: &mut InputRef<'a, '_, I, E>,
            cfg: Self::Config,
        ) -> PResult<Check, $O> {
            ConfigParserSealed::<I, $O, E>::go_cfg::<Check>(self, inp, cfg)
        }
    };
}

mod blanket;
#[cfg(feature = "unstable")]
pub mod cache;
pub mod combinator;
pub mod container;
#[cfg(feature = "either")]
mod either;
pub mod error;
#[cfg(feature = "extension")]
pub mod extension;
pub mod extra;
#[cfg(docsrs)]
pub mod guide;
pub mod input;
#[cfg(feature = "label")]
pub mod label;
#[cfg(feature = "lexical-numbers")]
pub mod number;
#[cfg(feature = "pratt")]
pub mod pratt;
pub mod primitive;
mod private;
pub mod recovery;
pub mod recursive;
#[cfg(feature = "regex")]
pub mod regex;
pub mod span;
mod stream;
pub mod text;
pub mod util;

/// Commonly used functions, traits and types.
///
/// *Listen, three eyes,” he said, “don’t you try to outweird me, I get stranger things than you free with my breakfast
/// cereal.”*
pub mod prelude {
    #[cfg(feature = "lexical-numbers")]
    pub use super::number::number;
    #[cfg(feature = "regex")]
    pub use super::regex::regex;
    pub use super::{
        error::{Cheap, EmptyErr, Error as _, Rich, Simple},
        extra,
        input::Input,
        primitive::{
            any, any_ref, choice, custom, empty, end, group, just, map_ctx, none_of, one_of, todo,
        },
        recovery::{nested_delimiters, skip_then_retry_until, skip_until, via_parser},
        recursive::{recursive, Recursive},
        span::{SimpleSpan, Span as _},
        text, Boxed, ConfigIterParser, ConfigParser, IterParser, ParseResult, Parser,
    };
    pub use crate::{select, select_ref};
}

use crate::input::InputOwn;
use alloc::{boxed::Box, string::String, vec, vec::Vec};
#[cfg(feature = "nightly")]
use core::marker::Tuple;
use core::{
    borrow::Borrow,
    cell::{Cell, RefCell},
    cmp::{Eq, Ordering},
    fmt,
    hash::Hash,
    marker::PhantomData,
    mem::MaybeUninit,
    ops::{Range, RangeFrom},
    panic::Location,
    str::FromStr,
};
use hashbrown::HashMap;
#[cfg(feature = "serde")]
use serde::{de::Visitor, Deserialize, Deserializer, Serialize, Serializer};

#[cfg(feature = "label")]
use self::label::{LabelError, Labelled};
use self::{
    combinator::*,
    container::*,
    error::Error,
    extra::ParserExtra,
    input::{
        BorrowInput, Emitter, ExactSizeInput, InputRef, MapExtra, SliceInput, StrInput, ValueInput,
    },
    prelude::*,
    primitive::Any,
    private::{
        Check, ConfigIterParserSealed, ConfigParserSealed, Emit, IPResult, IterParserSealed,
        Located, MaybeUninitExt, Mode, PResult, ParserSealed, Sealed,
    },
    recovery::{RecoverWith, Strategy},
    span::Span,
    text::*,
    util::{MaybeMut, MaybeRef},
};
#[cfg(all(feature = "extension", doc))]
use self::{extension::v1::*, primitive::custom, stream::Stream};

/// A type that allows mentioning type parameters *without* all of the customary omission of auto traits that comes
/// with `PhantomData`.
struct EmptyPhantom<T>(core::marker::PhantomData<T>);

impl<T> EmptyPhantom<T> {
    const fn new() -> Self {
        Self(core::marker::PhantomData)
    }
}

impl<T> Copy for EmptyPhantom<T> {}
impl<T> Clone for EmptyPhantom<T> {
    fn clone(&self) -> Self {
        *self
    }
}
// SAFETY: This is safe because `EmptyPhantom` doesn't actually contain a `T`.
unsafe impl<T> Send for EmptyPhantom<T> {}
// SAFETY: This is safe because `EmptyPhantom` doesn't actually contain a `T`.
unsafe impl<T> Sync for EmptyPhantom<T> {}
impl<T> Unpin for EmptyPhantom<T> {}
impl<T> core::panic::UnwindSafe for EmptyPhantom<T> {}
impl<T> core::panic::RefUnwindSafe for EmptyPhantom<T> {}

#[cfg(feature = "sync")]
mod sync {
    use super::*;

    pub(crate) type RefC<T> = alloc::sync::Arc<T>;
    pub(crate) type RefW<T> = alloc::sync::Weak<T>;
    pub(crate) type DynParser<'a, 'b, I, O, E> = dyn Parser<'a, I, O, E> + Send + Sync + 'b;

    /// A trait that requires either nothing or `Send` and `Sync` bounds depending on whether the `sync` feature is
    /// enabled. Used to constrain API usage succinctly and easily.
    pub trait MaybeSync: Send + Sync {}
    impl<T: Send + Sync> MaybeSync for T {}
}

#[cfg(not(feature = "sync"))]
mod sync {
    use super::*;

    pub(crate) type RefC<T> = alloc::rc::Rc<T>;
    pub(crate) type RefW<T> = alloc::rc::Weak<T>;
    pub(crate) type DynParser<'a, 'b, I, O, E> = dyn Parser<'a, I, O, E> + 'b;

    /// A trait that requires either nothing or `Send` and `Sync` bounds depending on whether the `sync` feature is
    /// enabled. Used to constrain API usage succinctly and easily.
    pub trait MaybeSync {}
    impl<T> MaybeSync for T {}
}

use sync::{DynParser, MaybeSync, RefC, RefW};

/// The result of performing a parse on an input with [`Parser`].
///
/// Unlike `Result`, this type is designed to express the fact that generating outputs and errors are not
/// mutually-exclusive operations: it is possible for a parse to produce non-terminal errors (see
/// [`Parser::recover_with`] while still producing useful output).
///
/// If you don't care for recovered outputs and you with to treat success/failure as a binary, you may use
/// [`ParseResult::into_result`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

    /// Get an iterator over the parse errors for this result. The iterator will produce no items if there were no
    /// errors.
    pub fn errors(&self) -> impl ExactSizeIterator<Item = &E> + DoubleEndedIterator {
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

    /// Convert this `ParseResult` into the output. If any errors were generated (including non-fatal errors!), a
    /// panic will occur instead.
    ///
    /// The use of this function is discouraged in user-facing code. However, it may be convenient for use in tests.
    #[track_caller]
    pub fn unwrap(self) -> T
    where
        E: fmt::Debug,
    {
        if self.has_errors() {
            panic!(
                "called `ParseResult::unwrap` on a parse result containing errors: {:?}",
                &self.errs
            )
        } else {
            self.output.expect("parser generated no errors or output")
        }
    }
}

/// A trait implemented by parsers.
///
/// Parsers take inputs of type `I`, which will implement [`Input`]. Refer to the documentation on [`Input`] for examples
/// of common input types. It will then attempt to parse them into a value of type `O`, which may be just about any type.
/// In doing so, they may encounter errors. These need not be fatal to the parsing process: syntactic errors can be
/// recovered from and a valid output may still be generated alongside any syntax errors that were encountered along the
/// way. Usually, this output comes in the form of an
/// [Abstract Syntax Tree](https://en.wikipedia.org/wiki/Abstract_syntax_tree) (AST).
///
/// The final type parameter, `E`, is expected to be one of the type in the [`extra`] module,
/// implementing [`ParserExtra`]. This trait is used to encapsulate the various types a parser
/// uses that are not simply its input and output. Refer to the documentation on the [`ParserExtra`] trait
/// for more detail on the contained types. If not provided, it will default to [`extra::Default`],
/// which will have the least overhead, but also the least meaningful errors.
///
/// The lifetime of the parser is used for zero-copy output - the input is bound by the lifetime,
/// and returned values or parser state may take advantage of this to borrow tokens or slices of the
/// input and hold on to them, if the input supports this.
///
/// You cannot directly implement this trait yourself. If you feel like the built-in parsers are not enough for you,
/// there are several options in increasing order of complexity:
///
/// 1) Try using combinators like [`Parser::try_map`] and [`Parser::validate`] to implement custom error generation
///
/// 2) Use [`custom`] to implement your own parsing logic inline within an existing parser
///
/// 3) Use chumsky's [`extension`] API to write an extension parser that feels like it's native to chumsky
///
/// 4) If you believe you've found a common use-case that's missing from chumsky, you could open a pull request to
///    implement it in chumsky itself.
#[cfg_attr(
    feature = "nightly",
    diagnostic::on_unimplemented(
        message = "The following is not a parser from `{I}` to `{O}`: `{Self}`",
        label = "This parser is not compatible because it does not implement `Parser<{I}, {O}, E>`",
        note = "You should check that the output types of your parsers are consistent with the combinators you're using",
    )
)]
pub trait Parser<'a, I: Input<'a>, O, E: ParserExtra<'a, I> = extra::Default>:
    ParserSealed<'a, I, O, E>
{
    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way.
    ///
    /// If `None` is returned (i.e: parsing failed) then there will *always* be at least one item in the error `Vec`.
    /// If you want to include non-default state, use [`Parser::parse_with_state`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[T]`], a [`&str`], [`Stream`], or anything implementing [`Input`] to it.
    fn parse(&self, input: I) -> ParseResult<O, E::Error>
    where
        I: Input<'a>,
        E::State: Default,
        E::Context: Default,
    {
        self.parse_with_state(input, &mut E::State::default())
    }

    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way.
    /// The provided state will be passed on to parsers that expect it, such as [`map_with`](Parser::map_with).
    ///
    /// If `None` is returned (i.e: parsing failed) then there will *always* be at least one item in the error `Vec`.
    /// If you want to just use a default state value, use [`Parser::parse`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[T]`], a [`&str`], [`Stream`], or anything implementing [`Input`] to it.
    fn parse_with_state(&self, input: I, state: &mut E::State) -> ParseResult<O, E::Error>
    where
        I: Input<'a>,
        E::Context: Default,
    {
        let mut own = InputOwn::new_state(input, state);
        let mut inp = own.as_ref_start();
        let res = self.then_ignore(end()).go::<Emit>(&mut inp);
        let alt = inp.errors.alt.take();
        let mut errs = own.into_errs();
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
        let mut own = InputOwn::new_state(input, state);
        let mut inp = own.as_ref_start();
        let res = self.then_ignore(end()).go::<Check>(&mut inp);
        let alt = inp.errors.alt.take();
        let mut errs = own.into_errs();
        let out = match res {
            Ok(()) => Some(()),
            Err(()) => {
                errs.push(alt.expect("error but no alt?").err);
                None
            }
        };
        ParseResult::new(out, errs)
    }

    /// Convert the output of this parser into a slice of the input, based on the current parser's
    /// span.
    fn to_slice(self) -> ToSlice<Self, O>
    where
        Self: Sized,
    {
        ToSlice {
            parser: self,
            phantom: EmptyPhantom::new(),
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
            phantom: EmptyPhantom::new(),
        }
    }

    /// Map the output of this parser to another value, with the opportunity to get extra metadata.
    ///
    /// The output type of this parser is `U`, the same as the function's output.
    ///
    /// # Examples
    ///
    /// Using the span of the output in the mapping function:
    ///
    /// ```
    /// # use chumsky::prelude::*;
    ///
    /// // It's common for AST nodes to use a wrapper type that allows attaching span information to them
    /// #[derive(Debug, PartialEq)]
    /// pub struct Spanned<T>(T, SimpleSpan<usize>);
    ///
    /// let ident = text::ascii::ident::<_, _, extra::Err<Simple<char>>>()
    ///     .map_with(|ident, e| Spanned(ident, e.span())) // Equivalent to `.map_with_span(|ident, span| Spanned(ident, span))`
    ///     .padded();
    ///
    /// assert_eq!(ident.parse("hello").into_result(), Ok(Spanned("hello", (0..5).into())));
    /// assert_eq!(ident.parse("       hello   ").into_result(), Ok(Spanned("hello", (7..12).into())));
    /// ```
    ///
    /// Using the parser state in the mapping function to intern strings:
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// use std::ops::Range;
    /// use lasso::{Rodeo, Spur};
    ///
    /// // It's common for AST nodes to use interned versions of identifiers
    /// // Keys are generally smaller, faster to compare, and can be `Copy`
    /// #[derive(Copy, Clone)]
    /// pub struct Ident(Spur);
    ///
    /// let ident = text::ascii::ident::<_, _, extra::Full<Simple<char>, Rodeo, ()>>()
    ///     .map_with(|ident, e| Ident(e.state().get_or_intern(ident)))
    ///     .padded()
    ///     .repeated()
    ///     .at_least(1)
    ///     .collect::<Vec<_>>();
    ///
    /// // Test out parser
    ///
    /// let mut interner = Rodeo::new();
    ///
    /// match ident.parse_with_state("hello", &mut interner).into_result() {
    ///     Ok(idents) => {
    ///         assert_eq!(interner.resolve(&idents[0].0), "hello");
    ///     }
    ///     Err(e) => panic!("Parsing Failed: {:?}", e),
    /// }
    ///
    /// match ident.parse_with_state("hello hello", &mut interner).into_result() {
    ///     Ok(idents) => {
    ///         assert_eq!(idents[0].0, idents[1].0);
    ///     }
    ///     Err(e) => panic!("Parsing Failed: {:?}", e),
    /// }
    /// ```
    ///
    /// Using the parse context in the mapping function:
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Simple};
    ///
    /// fn palindrome_parser<'a>() -> impl Parser<'a, &'a str, String> {
    ///     recursive(|chain| {
    ///         choice((
    ///             just(String::new())
    ///                 .configure(|cfg, ctx: &String| cfg.seq(ctx.clone()))
    ///                 .then_ignore(end()),
    ///             any()
    ///                 .map_with(|x, e| format!("{x}{}", e.ctx()))
    ///                 .ignore_with_ctx(chain),
    ///         ))
    ///     })
    ///     .with_ctx(String::new())
    /// }
    ///
    /// assert_eq!(palindrome_parser().parse("abccba").into_result().as_deref(), Ok("cba"));
    /// assert_eq!(palindrome_parser().parse("hello  olleh").into_result().as_deref(), Ok(" olleh"));
    /// assert!(palindrome_parser().parse("abccb").into_result().is_err());
    /// ```
    fn map_with<U, F: Fn(O, &mut MapExtra<'a, '_, '_, I, E>) -> U>(
        self,
        f: F,
    ) -> MapWith<Self, O, F>
    where
        Self: Sized,
    {
        MapWith {
            parser: self,
            mapper: f,
            phantom: EmptyPhantom::new(),
        }
    }

    /// Map the output of this parser to another value.
    /// If the output of this parser isn't a tuple, use [`Parser::map`].
    ///
    /// The output type of this parser is `U`, the same as the function's output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    ///  pub enum Value {
    ///       One(u8),
    ///      Two(u8, u8),
    ///      Three(u8, u8, u8),
    /// }
    ///
    /// fn parser<'a>() -> impl Parser<'a, &'a [u8], Vec<Value>> {
    ///     choice((
    ///         just(1).ignore_then(any()).map(Value::One),
    ///         just(2)
    ///             .ignore_then(group((any(), any())))
    ///             .map_group(Value::Two),
    ///         just(3)
    ///             .ignore_then(group((any(), any(), any())))
    ///             .map_group(Value::Three),
    ///     ))
    ///     .repeated()
    ///     .collect()
    /// }
    ///
    /// let bytes = &[3, 1, 2, 3, 1, 127, 2, 21, 69];
    /// assert_eq!(
    ///     parser().parse(bytes).into_result(),
    ///     Ok(vec![
    ///         Value::Three(1, 2, 3),
    ///         Value::One(127),
    ///         Value::Two(21, 69)
    ///     ])
    /// );
    /// ```
    #[cfg(feature = "nightly")]
    fn map_group<F: Fn<O>>(self, f: F) -> MapGroup<Self, O, F>
    where
        Self: Sized,
        O: Tuple,
    {
        MapGroup {
            parser: self,
            mapper: f,
            phantom: EmptyPhantom::new(),
        }
    }

    /// Transform the output of this parser to the pattern's span.
    ///
    /// This is commonly used when you know what pattern you've parsed and are only interested in the span of the
    /// pattern.
    ///
    /// The output type of this parser is `I::Span`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    ///
    /// // It's common for AST nodes to use a wrapper type that allows attaching span information to them
    /// #[derive(Debug, PartialEq)]
    /// pub enum Expr<'a> {
    ///     Int(&'a str, SimpleSpan),
    ///     // The span is that of the operator, '+'
    ///     Add(Box<Expr<'a>>, SimpleSpan, Box<Expr<'a>>),
    /// }
    ///
    /// let int = text::int::<_, _, extra::Err<Simple<char>>>(10)
    ///     .to_slice()
    ///     .map_with(|int, e| Expr::Int(int, e.span()))
    ///     .padded();
    ///
    /// let add_op = just('+').to_span().padded();
    /// let sum = int.foldl(
    ///     add_op.then(int).repeated(),
    ///     |a, (op_span, b)| Expr::Add(Box::new(a), op_span, Box::new(b)),
    /// );
    ///
    /// assert_eq!(sum.parse("42 + 7 + 13").into_result(), Ok(Expr::Add(
    ///     Box::new(Expr::Add(
    ///         Box::new(Expr::Int("42", (0..2).into())),
    ///         (3..4).into(),
    ///         Box::new(Expr::Int("7", (5..6).into())),
    ///     )),
    ///     (7..8).into(),
    ///     Box::new(Expr::Int("13", (9..11).into())),
    /// )));
    /// ```
    fn to_span(self) -> ToSpan<Self, O>
    where
        Self: Sized,
    {
        ToSpan {
            parser: self,
            phantom: EmptyPhantom::new(),
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
            phantom: EmptyPhantom::new(),
        }
    }

    /// After a successful parse, apply a fallible function to the output, with the opportunity to get extra metadata.
    /// If the function produces an error, treat it as a parsing error.
    ///
    /// If you wish parsing of this pattern to continue when an error is generated instead of halting, consider using
    /// [`Parser::validate`] instead.
    ///
    /// The output type of this parser is `U`, the [`Ok`] return value of the function.
    fn try_map_with<U, F: Fn(O, &mut MapExtra<'a, '_, '_, I, E>) -> Result<U, E::Error>>(
        self,
        f: F,
    ) -> TryMapWith<Self, O, F>
    where
        Self: Sized,
    {
        TryMapWith {
            parser: self,
            mapper: f,
            phantom: EmptyPhantom::new(),
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
            phantom: EmptyPhantom::new(),
        }
    }

    /// Memoize the parser such that later attempts to parse the same input 'remember' the attempt and exit early.
    ///
    /// If you're finding that certain inputs produce exponential behavior in your parser, strategically applying
    /// memoization to a ['garden path'](https://en.wikipedia.org/wiki/Garden-path_sentence) rule is often an effective
    /// way to solve the problem. At the limit, applying memoization to all combinators will turn any parser into one
    /// with `O(n)`, albeit with very significant per-element overhead and high memory usage.
    ///
    /// Memoization also works with recursion, so this can be used to write parsers using
    /// [left recursion](https://en.wikipedia.org/wiki/Left_recursion).
    // TODO: Example
    #[cfg(feature = "memoization")]
    fn memoized(self) -> Memoized<Self>
    where
        Self: Sized,
    {
        Memoized { parser: self }
    }

    /// Transform all outputs of this parser to a predetermined value.
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
    fn to<U: Clone>(self, to: U) -> To<Self, O, U>
    where
        Self: Sized,
    {
        To {
            parser: self,
            to,
            phantom: EmptyPhantom::new(),
        }
    }

    /// Label this parser with the given label.
    ///
    /// Labelling a parser makes all errors generated by the parser refer to the label rather than any sub-elements
    /// within the parser. For example, labelling a parser for an expression would yield "expected expression" errors
    /// rather than "expected integer, string, binary op, etc." errors.
    // TODO: Example
    #[cfg(feature = "label")]
    fn labelled<L>(self, label: L) -> Labelled<Self, L>
    where
        Self: Sized,
        E::Error: LabelError<'a, I, L>,
    {
        Labelled {
            parser: self,
            label,
            is_context: false,
        }
    }

    /// Parse one thing and then another thing, yielding a tuple of the two outputs.
    ///
    /// The output type of this parser is `(O, U)`, a combination of the outputs of both parsers.
    ///
    /// If you instead only need the output of __one__ of the parsers, use [`ignore_then`](Self::ignore_then)
    /// or [`then_ignore`](Self::then_ignore).
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
            phantom: EmptyPhantom::new(),
        }
    }

    /// Parse one thing and then another thing, yielding only the output of the latter.
    ///
    /// The output type of this parser is `U`, the same as the second parser.
    ///
    /// If you instead only need the output of the first parser, use [`then_ignore`](Self::then_ignore).
    /// If you need the output of __both__ parsers, use [`then`](Self::then).
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
            phantom: EmptyPhantom::new(),
        }
    }

    /// Parse one thing and then another thing, yielding only the output of the former.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// If you instead only need the output of the second parser, use [`ignore_then`](Self::ignore_then).
    /// If you need the output of __both__ parsers, use [`then`](Self::then).
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
            phantom: EmptyPhantom::new(),
        }
    }

    /// Parse input as part of a token-tree - using an input generated from within the current
    /// input. In other words, this parser will attempt to create a *new* input stream from within
    /// the one it is being run on, and the parser it was called on will be provided this *new* input.
    /// By default, the original parser is expected to consume up to the end of the new stream. To
    /// allow only consuming part of the stream, use [`Parser::lazy`] to ignore trailing tokens.
    ///
    /// The provided parser `P` is expected to have both an input and output type which match the input
    /// type of the parser it is called on. As an example, if the original parser takes an input of
    /// `Stream<Iterator<Item = T>>`, `P` will be run first against that input, and is expected to
    /// output a new `Stream<Iterator<Item = T>>` which the original parser will be run against.
    ///
    /// The output of this parser is `O`, the output of the parser it is called on.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, util::MaybeRef, error::Simple};
    /// #[derive(Debug, Clone, PartialEq)]
    /// enum Token<'a> {
    ///     Struct,
    ///     Ident(&'a str),
    ///     Item(&'a str),
    ///     Group(Vec<Token<'a>>),
    /// }
    ///
    /// let group = select_ref! { Token::Group(g) => g.as_slice() };
    ///
    /// let ident = select_ref! { Token::Ident(i) => *i };
    ///
    /// let items = select_ref! { Token::Item(i) => *i }
    ///     .repeated()
    ///     .collect::<Vec<_>>()
    ///     .nested_in(group);
    ///
    /// let struc = just::<_, _, extra::Err<Simple<_>>>(&Token::Struct)
    ///     .ignore_then(ident)
    ///     .then(items);
    ///
    /// let tl = struc
    ///     .repeated()
    ///     .collect::<Vec<_>>();
    ///
    /// let tokens = [
    ///     Token::Struct,
    ///     Token::Ident("foo"),
    ///     Token::Group(vec![
    ///         Token::Item("a"),
    ///         Token::Item("b"),
    ///     ]),
    /// ];
    ///
    /// assert_eq!(tl.parse(&tokens).into_result(), Ok(vec![("foo", vec!["a", "b"])]));
    /// ```
    fn nested_in<B: Parser<'a, I, I, E>>(self, other: B) -> NestedIn<Self, B, O, E>
    where
        Self: Sized,
        I: 'a,
    {
        NestedIn {
            parser_a: self,
            parser_b: other,
            phantom: EmptyPhantom::new(),
        }
    }

    /// Parse one thing and then another thing, creating the second parser from the result of
    /// the first. If you don't need the context in the output, use [`Parser::then_with_ctx`].
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
    ///     .ignore_with_ctx(successor);
    ///
    /// assert_eq!(successive_letters.parse(b"ab").into_result(), Ok(b'b')); // 'b' follows 'a'
    /// assert!(successive_letters.parse(b"ac").has_errors()); // 'c' does not follow 'a'
    /// ```
    fn ignore_with_ctx<U, P>(
        self,
        then: P,
    ) -> IgnoreWithCtx<Self, P, O, I, extra::Full<E::Error, E::State, O>>
    where
        Self: Sized,
        O: 'a,
        P: Parser<'a, I, U, extra::Full<E::Error, E::State, O>>,
    {
        IgnoreWithCtx {
            parser: self,
            then,
            phantom: EmptyPhantom::new(),
        }
    }

    /// Parse one thing and then another thing, creating the second parser from the result of
    /// the first. If you don't need the context in the output, prefer [`Parser::ignore_with_ctx`].
    ///
    /// The output of this parser is `(E::Context, O)`,
    /// a combination of the context and the output of the parser.
    ///
    /// Error recovery for this parser may be sub-optimal, as if the first parser succeeds on
    /// recovery then the second produces an error, the primary error will point to the location in
    /// the second parser which failed, ignoring that the first parser may be the root cause. There
    /// may be other pathological errors cases as well.
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
            phantom: EmptyPhantom::new(),
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

    /// TODO
    fn with_state<State>(self, state: State) -> WithState<Self, State>
    where
        Self: Sized,
        State: 'a + Clone,
    {
        WithState {
            parser: self,
            state,
        }
    }

    /// Applies both parsers to the same position in the input, succeeding
    /// only if both succeed. The returned value will be that of the first parser,
    /// and the input will be at the end of the first parser if `and_is` succeeds.
    ///
    /// The second parser is allowed to consume more or less input than the first parser,
    /// but like its output, how much it consumes won't affect the final result.
    ///
    /// The motivating use-case is in combination with [`Parser::not`], allowing a parser
    /// to consume something only if it isn't also something like an escape sequence or a nested block.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Simple};
    ///
    /// let escape = just("\\n").to('\n');
    ///
    /// // C-style string literal
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
            phantom: EmptyPhantom::new(),
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
            phantom: EmptyPhantom::new(),
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
    /// let ident = text::ascii::ident::<_, _, extra::Err<Simple<char>>>()
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
            phantom: EmptyPhantom::new(),
        }
    }

    /// Parse one thing or, on failure, another thing.
    ///
    /// The output of both parsers must be of the same type, because either output can be produced.
    ///
    /// If both parser succeed, the output of the first parser is guaranteed to be prioritized over the output of the
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

    /// Invert the result of the contained parser, failing if it succeeds and succeeding if it fails.
    /// The output of this parser is always `()`, the unit type.
    ///
    /// The motivating case for this is in combination with [`Parser::and_is`], allowing a parser
    /// to consume something only if it isn't also something like an escape sequence or a nested block.
    ///
    /// Caveats:
    /// - The error message produced by `not` by default will likely be fairly unhelpful - it can
    ///   only tell the span that was wrong.
    /// - If not careful, it's fairly easy to create non-intuitive behavior due to end-of-input
    ///   being a valid token for a parser to consume, and as most parsers fail at end of input,
    ///   `not` will succeed on it.
    ///
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
    ///         .to_slice()
    ///         .map(Tree::Text);
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
            phantom: EmptyPhantom::new(),
        }
    }

    /// Parse a pattern zero or more times (analog to Regex's `<PAT>*`).
    ///
    /// Input is eagerly parsed. Be aware that the parser will accept no occurrences of the pattern too. Consider using
    /// [`Repeated::at_least`] instead if you wish to parse a minimum number of elements.
    ///
    /// The output type of this parser is, by default, `()`. If you want to collect the items into a [`Container`]
    /// (such as a [`Vec`]), use [`IterParser::collect`].
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
    #[cfg_attr(debug_assertions, track_caller)]
    fn repeated(self) -> Repeated<Self, O, I, E>
    where
        Self: Sized,
    {
        Repeated {
            parser: self,
            at_least: 0,
            at_most: !0,
            #[cfg(debug_assertions)]
            location: *Location::caller(),
            phantom: EmptyPhantom::new(),
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
    /// let shopping = text::ascii::ident::<_, _, extra::Err<Simple<char>>>()
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .collect::<Vec<_>>();
    ///
    /// assert_eq!(shopping.parse("eggs").into_result(), Ok(vec!["eggs"]));
    /// assert_eq!(shopping.parse("eggs, flour, milk").into_result(), Ok(vec!["eggs", "flour", "milk"]));
    /// ```
    ///
    /// See [`SeparatedBy::allow_leading`] and [`SeparatedBy::allow_trailing`] for more examples.
    #[cfg_attr(debug_assertions, track_caller)]
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
            #[cfg(debug_assertions)]
            location: *Location::caller(),
            phantom: EmptyPhantom::new(),
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
    #[cfg_attr(debug_assertions, track_caller)]
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
            #[cfg(debug_assertions)]
            location: *Location::caller(),
            phantom: EmptyPhantom::new(),
        }
    }

    /// Left-fold the output of the parser into a single value, making use of the parser's state when doing so.
    ///
    /// The output of the original parser must be of type `(A, impl IntoIterator<Item = B>)`.
    ///
    /// The output type of this parser is `A`, the left-hand component of the original parser's output.
    ///
    /// # Examples
    ///
    /// ## General
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Simple};
    /// let int = text::int::<_, _, extra::Full<Simple<char>, i32, ()>>(10)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let sum = int
    ///     .clone()
    ///     .foldl_with(just('+').ignore_then(int).repeated(), |a, b, e| (a + b) * *e.state());
    ///
    /// let mut multiplier = 2i32;
    /// assert_eq!(sum.parse_with_state("1+12+3+9", &mut multiplier).into_result(), Ok(134));
    /// assert_eq!(sum.parse_with_state("6", &mut multiplier).into_result(), Ok(6));
    /// ```
    ///
    /// ## Interning / Arena Allocation
    ///
    /// This example assumes use of the `slotmap` crate for arena allocation.
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// use slotmap::{new_key_type, SlotMap};
    ///
    /// // Metadata type for node Ids for extra type safety
    /// new_key_type! {
    ///    pub struct NodeId;
    /// }
    ///
    /// // AST nodes reference other nodes with `NodeId`s instead of containing boxed/owned values
    /// #[derive(Copy, Clone, Debug, PartialEq)]
    /// enum Expr {
    ///     Int(i32),
    ///     Add(NodeId, NodeId),
    /// }
    ///
    /// type NodeArena = SlotMap<NodeId, Expr>;
    ///
    /// // Now, define our parser
    /// let int = text::int::<&str, _, extra::Full<Simple<char>, NodeArena, ()>>(10)
    ///     .padded()
    ///     .map_with(|s, e|
    ///         // Return the ID of the new integer node
    ///         e.state().insert(Expr::Int(s.parse().unwrap()))
    ///     );
    ///
    /// let sum = int.foldl_with(
    ///     just('+').padded().ignore_then(int).repeated(),
    ///     |a: NodeId, b: NodeId, e| {
    ///         // Inserting an item into the arena returns its ID
    ///         e.state().insert(Expr::Add(a, b))
    ///     }
    /// );
    ///
    /// // Test our parser
    /// let mut arena = NodeArena::default();
    /// let four_plus_eight = sum.parse_with_state("4 + 8", &mut arena).unwrap();
    /// if let Expr::Add(a, b) = arena[four_plus_eight] {
    ///     assert_eq!(arena[a], Expr::Int(4));
    ///     assert_eq!(arena[b], Expr::Int(8));
    /// } else {
    ///     panic!("Not an Expr::Add");
    /// }
    /// ```
    #[cfg_attr(debug_assertions, track_caller)]
    fn foldl_with<B, F, OB>(self, other: B, f: F) -> FoldlWith<F, Self, B, OB, E>
    where
        F: Fn(O, OB, &mut MapExtra<'a, '_, '_, I, E>) -> O,
        B: IterParser<'a, I, OB, E>,
        Self: Sized,
    {
        FoldlWith {
            parser_a: self,
            parser_b: other,
            folder: f,
            #[cfg(debug_assertions)]
            location: *Location::caller(),
            phantom: EmptyPhantom::new(),
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
    ///     .to_slice()
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
    /// let ident = text::ascii::ident::<_, _, extra::Err<Simple<char>>>().padded();
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

    // /// Flatten a nested collection.
    // ///
    // /// This use-cases of this method are broadly similar to those of [`Iterator::flatten`].
    // ///
    // /// The output type of this parser is `Vec<T>`, where the original parser output was
    // /// `impl IntoIterator<Item = impl IntoIterator<Item = T>>`.
    // fn flatten<T, Inner>(self) -> Map<Self, O, fn(O) -> Vec<T>>
    // where
    //     Self: Sized,
    //     O: IntoIterator<Item = Inner>,
    //     Inner: IntoIterator<Item = T>,
    // {
    //     self.map(|xs| xs.into_iter().flat_map(|xs| xs.into_iter()).collect())
    // }

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

    // /// Map the primary error of this parser to another value, making use of the span from the start of the attempted
    // /// to the point at which the error was encountered.
    // ///
    // /// This function is useful for augmenting errors to allow them to display the span of the initial part of a
    // /// pattern, for example to add a "while parsing" clause to your error messages.
    // ///
    // /// The output type of this parser is `O`, the same as the original parser.
    // ///
    // // TODO: Map E -> D, not E -> E
    // fn map_err_with_span<F>(self, f: F) -> MapErrWithSpan<Self, F>
    // where
    //     Self: Sized,
    //     F: Fn(E::Error, I::Span) -> E::Error,
    // {
    //     MapErrWithSpan {
    //         parser: self,
    //         mapper: f,
    //     }
    // }

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

    /// Validate an output, producing non-terminal errors if it does not fulfill certain criteria.
    /// The errors will not immediately halt parsing on this path, but instead it will continue,
    /// potentially emitting one or more other errors, only failing after the pattern has otherwise
    /// successfully, or emitted another terminal error.
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
    ///     .validate(|x: u32, e, emitter| {
    ///         if x < 256 { emitter.emit(Rich::custom(e.span(), format!("{} must be 256 or higher.", x))) }
    ///         x
    ///     });
    ///
    /// assert_eq!(large_int.parse("537").into_result(), Ok(537));
    /// assert!(large_int.parse("243").into_result().is_err());
    /// ```
    ///
    /// To show the difference in behavior from [`Parser::try_map`]:
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// # use chumsky::util::MaybeRef;
    /// # use chumsky::error::Error;
    /// // start with the same large_int validator
    /// let large_int_val = text::int::<_, _, extra::Err<Rich<char>>>(10)
    ///         .from_str()
    ///         .unwrapped()
    ///         .validate(|x: u32, e, emitter| {
    ///             if x < 256 { emitter.emit(Rich::custom(e.span(), format!("{} must be 256 or higher", x))) }
    ///             x
    ///         });
    ///
    /// // A try_map version of the same parser
    /// let large_int_tm = text::int::<_, _, extra::Err<Rich<char>>>(10)
    ///         .from_str()
    ///         .unwrapped()
    ///         .try_map(|x: u32, span| {
    ///             if x < 256 {
    ///                 Err(Rich::custom(span, format!("{} must be 256 or higher", x)))
    ///             } else {
    ///                 Ok(x)
    ///             }
    ///         });
    ///
    /// // Parser that uses the validation version
    /// let multi_step_val = large_int_val.then(text::ascii::ident().padded());
    /// // Parser that uses the try_map version
    /// let multi_step_tm = large_int_tm.then(text::ascii::ident().padded());
    ///
    /// // On success, both parsers are equivalent
    /// assert_eq!(
    ///     multi_step_val.parse("512 foo").into_result(),
    ///     Ok((512, "foo"))
    /// );
    ///
    /// assert_eq!(
    ///     multi_step_tm.parse("512 foo").into_result(),
    ///     Ok((512, "foo"))
    /// );
    ///
    /// // However, on failure, they may produce different errors:
    /// assert_eq!(
    ///     multi_step_val.parse("100 2").into_result(),
    ///     Err(vec![
    ///         Rich::<char>::custom((0..3).into(), "100 must be 256 or higher"),
    ///         <Rich<char> as Error<&str>>::expected_found([], Some(MaybeRef::Val('2')), (4..5).into()),
    ///     ])
    /// );
    ///
    /// assert_eq!(
    ///     multi_step_tm.parse("100 2").into_result(),
    ///     Err(vec![Rich::<char>::custom((0..3).into(), "100 must be 256 or higher")])
    /// );
    /// ```
    ///
    /// As is seen in the above example, validation doesn't prevent the emission of later errors in the
    /// same parser, but still produces an error in the output.
    ///
    fn validate<U, F>(self, f: F) -> Validate<Self, O, F>
    where
        Self: Sized,
        F: Fn(O, &mut MapExtra<'a, '_, '_, I, E>, &mut Emitter<E::Error>) -> U,
    {
        Validate {
            parser: self,
            validator: f,
            phantom: EmptyPhantom::new(),
        }
    }

    // /// Map the primary error of this parser to a result. If the result is [`Ok`], the parser succeeds with that value.
    // ///
    // /// Note that, if the closure returns [`Err`], the parser will not consume any input.
    // ///
    // /// The output type of this parser is `U`, the [`Ok`] type of the result.
    // fn or_else<F>(self, f: F) -> OrElse<Self, F>
    // where
    //     Self: Sized,
    //     F: Fn(E::Error) -> Result<O, E::Error>,
    // {
    //     OrElse {
    //         parser: self,
    //         or_else: f,
    //     }
    // }

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
    #[track_caller]
    fn unwrapped(self) -> Unwrapped<Self, O>
    where
        Self: Sized,
    {
        Unwrapped {
            parser: self,
            location: *Location::caller(),
            phantom: EmptyPhantom::new(),
        }
    }

    /// Turn this [`Parser`] into an [`IterParser`] if its output type implements [`IntoIterator`].
    ///
    /// The resulting iterable parser will emit each element of the output type in turn.
    ///
    /// This is *broadly* analogous to functions like [`Vec::into_iter`], but operating at the level of parser outputs.
    // TODO: Example
    fn into_iter(self) -> IntoIter<Self, O>
    where
        Self: Sized,
        O: IntoIterator,
    {
        IntoIter {
            parser: self,
            phantom: EmptyPhantom::new(),
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
    ///
    /// # Examples
    ///
    /// When not using `boxed`, the following patterns are either impossible or very difficult to express:
    ///
    /// ```compile_fail
    /// # use chumsky::prelude::*;
    ///
    /// pub trait Parseable: Sized {
    ///     type Parser<'a>: Parser<'a, &'a str, Self>;
    ///
    ///     fn parser<'a>() -> Self::Parser<'a>;
    /// }
    ///
    /// impl Parseable for i32 {
    ///     // We *can* write this type, but it will be very impractical, and change on any alterations
    ///     // to the implementation
    ///     type Parser<'a> = ???;
    ///
    ///     fn parser<'a>() -> Self::Parser<'a> {
    ///         todo()
    ///     }
    /// }
    /// ```
    ///
    /// ```compile_fail
    /// # use chumsky::prelude::*;
    /// # fn user_input<'a>() -> impl IntoIterator<Item = impl Parser<'a, &'a str, char>> { [just('b')] }
    ///
    /// let user_input = user_input();
    ///
    /// let mut parser = just('a');
    /// for i in user_input {
    ///     // Doesn't work due to type mismatch - since every combinator creates a unique type
    ///     parser = parser.or(i);
    /// }
    ///
    /// let parser = parser.then(just('z'));
    /// let _ = parser.parse("b").into_result();
    /// ```
    ///
    /// However, with `boxed`, we can express them by making the parsers all share a common type:
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// pub trait Parseable: Sized {
    ///     fn parser<'a>() -> Boxed<'a, 'a, &'a str, Self, extra::Default>;
    /// }
    ///
    /// impl Parseable for i32 {
    ///     fn parser<'a>() -> Boxed<'a, 'a, &'a str, Self, extra::Default> {
    ///         todo().boxed()
    ///     }
    /// }
    /// ```
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// # fn user_input<'a>() -> impl IntoIterator<Item = impl Parser<'a, &'a str, char>> { [just('b'), just('c')] }
    /// let user_input = user_input();
    /// let mut parser = just('a').boxed();
    /// for i in user_input {
    ///     // Doesn't work due to type mismatch - since every combinator creates a unique type
    ///     parser = parser.or(i).boxed();
    /// }
    /// let parser = parser.then(just('z'));
    /// parser.parse("az").into_result().unwrap();
    /// ```
    ///
    fn boxed<'b>(self) -> Boxed<'a, 'b, I, O, E>
    where
        Self: MaybeSync + Sized + 'a + 'b,
    {
        ParserSealed::boxed(self)
    }

    /// Use [Pratt parsing](https://en.wikipedia.org/wiki/Operator-precedence_parser#Pratt_parsing) to ergonomically
    /// parse this pattern separated by prefix, postfix, and infix operators of various associativites and precedence.
    ///
    /// Pratt parsing is a powerful technique and is recommended when writing parsers for expressions.
    ///
    /// # Example
    ///
    /// See the documentation in [`pratt`] for more extensive examples and details.
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// use chumsky::pratt::*;
    /// use std::ops::{Neg, Mul, Div, Add, Sub};
    ///
    /// let int = text::int::<_, _, extra::Err<Rich<char>>>(10)
    ///     .from_str()
    ///     .unwrapped()
    ///     .padded();
    ///
    /// let op = |c| just(c).padded();
    ///
    /// let expr = int.pratt((
    ///     prefix(2, op('-'), i64::neg),
    ///     infix(left(1), op('*'), i64::mul),
    ///     infix(left(1), op('/'), i64::div),
    ///     infix(left(0), op('+'), i64::add),
    ///     infix(left(0), op('-'), i64::sub),
    /// ));
    ///
    /// // Pratt parsing can handle unary operators...
    /// assert_eq!(expr.parse("-7").into_result(), Ok(-7));
    /// // ...and infix binary operators...
    /// assert_eq!(expr.parse("6 + 3").into_result(), Ok(9));
    /// // ...and arbitrary precedence levels between them.
    /// assert_eq!(expr.parse("2 + 3 * -4").into_result(), Ok(-10));
    /// ```
    #[cfg(feature = "pratt")]
    fn pratt<Ops>(self, ops: Ops) -> pratt::Pratt<Self, Ops>
    where
        Self: Sized,
    {
        pratt::Pratt { atom: self, ops }
    }
}

#[cfg(feature = "nightly")]
impl<'a, I, O, E> ParserSealed<'a, I, O, E> for !
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    fn go<M: Mode>(&self, _inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        *self
    }

    go_extra!(O);
}

/// A [`Parser`] that can be configured with runtime context. This allows for context-sensitive parsing
/// of input. Note that chumsky only supports 'left'-sensitive parsing, where the context for a parser
/// is derived from earlier in the input.
///
/// Chumsky distinguishes 'state' from 'context'. State is not able to change what input a parser
/// accepts, but may be used to change the contents of the type it emits. In this way state is expected
/// to be idempotent - combinators such as [`Parser::map_with`] are allowed to not call the
/// provided closure at all if they don't emit any output. Context and configuration, on the other hand,
/// is used to change what kind of input a parser may accept, and thus must always be evaluated. Context
/// isn't usable in any map combinator however - while it may affect accepted input, it is not expected
/// to change the final result outside of how it changes what the parser itself returns.
///
/// Not all parsers currently support configuration. If you feel like you need a parser to be configurable
/// and it isn't currently, please open an issue on the issue tracker of the main repository.
pub trait ConfigParser<'a, I, O, E>: ConfigParserSealed<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    /// A combinator that allows configuration of the parser from the current context. Context
    /// is most often derived from [`Parser::ignore_with_ctx`], [`Parser::then_with_ctx`] or [`map_ctx`],
    /// and is how chumsky supports parsing things such as indentation-sensitive grammars.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    ///
    /// let int = text::int::<_, _, extra::Err<Rich<char>>>(10)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// // By default, accepts any number of items
    /// let item = text::ascii::ident()
    ///     .padded()
    ///     .repeated();
    ///
    /// // With configuration, we can declare an exact number of items based on a prefix length
    /// let len_prefixed_arr = int
    ///     .ignore_with_ctx(item.configure(|repeat, ctx| repeat.exactly(*ctx)).collect::<Vec<_>>());
    ///
    /// assert_eq!(
    ///     len_prefixed_arr.parse("2 foo bar").into_result(),
    ///     Ok(vec!["foo", "bar"]),
    /// );
    ///
    /// assert_eq!(
    ///     len_prefixed_arr.parse("0").into_result(),
    ///     Ok(vec![]),
    /// );
    ///
    /// len_prefixed_arr.parse("3 foo bar baz bam").into_result().unwrap_err();
    /// len_prefixed_arr.parse("3 foo bar").into_result().unwrap_err();
    /// ```
    fn configure<F>(self, cfg: F) -> Configure<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Config, &E::Context) -> Self::Config,
    {
        Configure { parser: self, cfg }
    }
}

/// An iterator that wraps an iterable parser. See [`IterParser::parse_iter`].
#[cfg(test)]
pub struct ParserIter<'a, 'iter, P: IterParser<'a, I, O, E>, I: Input<'a>, O, E: ParserExtra<'a, I>>
{
    parser: P,
    offset: I::Offset,
    own: InputOwn<'a, 'iter, I, E>,
    iter_state: Option<P::IterState<Emit>>,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(&'a (), O)>,
}

#[cfg(test)]
impl<'a, 'iter, P, I: Input<'a>, O, E: ParserExtra<'a, I>> Iterator
    for ParserIter<'a, 'iter, P, I, O, E>
where
    P: IterParser<'a, I, O, E>,
{
    type Item = O;

    fn next(&mut self) -> Option<Self::Item> {
        let mut inp = self.own.as_ref_at(self.offset);
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
        res.ok().and_then(|res| res)
    }
}

/// An iterable equivalent of [`Parser`], i.e: a parser that generates a sequence of outputs.
pub trait IterParser<'a, I, O, E = extra::Default>: IterParserSealed<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    /// Collect this iterable parser into a [`Container`].
    ///
    /// This is commonly useful for collecting parsers that output many values into containers of various kinds:
    /// [`Vec`]s, [`String`]s, or even [`HashMap`]s. This method is analogous to [`Iterator::collect`].
    ///
    /// The output type of this iterable parser is `C`, the type being collected into.
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
    #[cfg_attr(debug_assertions, track_caller)]
    fn collect<C: Container<O>>(self) -> Collect<Self, O, C>
    where
        Self: Sized,
    {
        Collect {
            parser: self,
            #[cfg(debug_assertions)]
            location: *Location::caller(),
            phantom: EmptyPhantom::new(),
        }
    }

    /// Collect this iterable parser into a [`ContainerExactly`].
    ///
    /// This is useful for situations where the number of items to consume is statically known.
    /// A common use-case is collecting into an array.
    ///
    /// The output type of this iterable parser if `C`, the type being collected into.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Simple};
    /// let three_digit = any::<_, extra::Err<Simple<char>>>().filter(|c: &char| c.is_numeric())
    ///     .repeated()
    ///     .collect_exactly::<[_; 3]>();
    ///
    /// assert_eq!(three_digit.parse("123").into_result(), Ok(['1', '2', '3']));
    /// assert!(three_digit.parse("12").into_result().is_err());
    /// assert!(three_digit.parse("1234").into_result().is_err());
    /// ```
    fn collect_exactly<C: ContainerExactly<O>>(self) -> CollectExactly<Self, O, C>
    where
        Self: Sized,
    {
        CollectExactly {
            parser: self,
            phantom: EmptyPhantom::new(),
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

    /// Enumerate outputs of this iterable parser.
    ///
    /// This function behaves in a similar way to [`Iterator::enumerate`].
    ///
    /// The output type of this iterable parser is `(usize, O)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Simple};
    /// let word = text::ascii::ident::<_, _, extra::Err<Simple<char>>>()
    ///     .padded()
    ///     .repeated() // This parser is iterable (i.e: implements `IterParser`)
    ///     .enumerate()
    ///     .collect::<Vec<(usize, &str)>>();
    ///
    /// assert_eq!(word.parse("hello world").into_result(), Ok(vec![(0, "hello"), (1, "world")]));
    /// ```
    fn enumerate(self) -> Enumerate<Self, O>
    where
        Self: Sized,
    {
        Enumerate {
            parser: self,
            phantom: EmptyPhantom::new(),
        }
    }

    /// Right-fold the output of the parser into a single value.
    ///
    /// The output of the original parser must be of type `(impl IntoIterator<Item = A>, B)`. Because right-folds work
    /// backwards, the iterator must implement [`DoubleEndedIterator`] so that it can be reversed.
    ///
    /// The output type of this iterable parser is `B`, the right-hand component of the original parser's output.
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
    #[cfg_attr(debug_assertions, track_caller)]
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
            #[cfg(debug_assertions)]
            location: *Location::caller(),
            phantom: EmptyPhantom::new(),
        }
    }

    /// Right-fold the output of the parser into a single value, making use of the parser's state when doing so.
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
    /// let int = text::int::<_, _, extra::Full<Simple<char>, i32, ()>>(10)
    ///     .from_str()
    ///     .unwrapped();
    ///
    /// let signed = just('+').to(1)
    ///     .or(just('-').to(-1))
    ///     .repeated()
    ///     .foldr_with(int, |a, b, e| {
    ///         *e.state() += 1;
    ///         a * b
    ///     });
    ///
    /// // Test our parser
    /// let mut folds = 0i32;
    /// assert_eq!(signed.parse_with_state("3", &mut folds).into_result(), Ok(3));
    /// assert_eq!(signed.parse_with_state("-17", &mut folds).into_result(), Ok(-17));
    /// assert_eq!(signed.parse_with_state("--+-+-5", &mut folds).into_result(), Ok(5));
    /// ```
    ///
    ///
    #[cfg_attr(debug_assertions, track_caller)]
    fn foldr_with<B, F, OA>(self, other: B, f: F) -> FoldrWith<F, Self, B, O, E>
    where
        F: Fn(O, OA, &mut MapExtra<'a, '_, '_, I, E>) -> OA,
        B: Parser<'a, I, OA, E>,
        Self: Sized,
    {
        FoldrWith {
            parser_a: self,
            parser_b: other,
            folder: f,
            #[cfg(debug_assertions)]
            location: *Location::caller(),
            phantom: EmptyPhantom::new(),
        }
    }

    /// TODO
    #[cfg(feature = "nightly")]
    fn flatten(self) -> Flatten<Self, O>
    where
        O: IntoIterator,
        Self: Sized,
    {
        Flatten {
            parser: self,
            phantom: EmptyPhantom::new(),
        }
    }

    /// Create an iterator over the outputs generated by an iterable parser.
    ///
    /// Warning: Trailing errors will be ignored
    // TODO: Stabilize once error handling is properly decided on
    #[cfg(test)]
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
                own: InputOwn::new(input),
                iter_state: None,
                phantom: EmptyPhantom::new(),
            }),
            Vec::new(),
        )
    }

    /// Create an iterator over the outputs generated by an iterable parser with the given parser state.
    ///
    /// Warning: Trailing errors will be ignored
    // TODO: Stabilize once error handling is properly decided on
    #[cfg(test)]
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
                own: InputOwn::new_state(input, state),
                iter_state: None,
                phantom: EmptyPhantom::new(),
            }),
            Vec::new(),
        )
    }
}

/// An iterable equivalent of [`ConfigParser`], i.e: a parser that generates a sequence of outputs and
/// can be configured at runtime.
pub trait ConfigIterParser<'a, I, O, E = extra::Default>:
    ConfigIterParserSealed<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    /// A combinator that allows configuration of the parser from the current context
    fn configure<F>(self, cfg: F) -> IterConfigure<Self, F, O>
    where
        Self: Sized,
        F: Fn(Self::Config, &E::Context) -> Self::Config,
    {
        IterConfigure {
            parser: self,
            cfg,
            phantom: EmptyPhantom::new(),
        }
    }

    /// A combinator that allows fallible configuration of the parser from the current context -
    /// if an error is returned, parsing fails.
    fn try_configure<F>(self, cfg: F) -> TryIterConfigure<Self, F, O>
    where
        Self: Sized,
        F: Fn(Self::Config, &E::Context, I::Span) -> Result<Self::Config, E::Error>,
    {
        TryIterConfigure {
            parser: self,
            cfg,
            phantom: EmptyPhantom::new(),
        }
    }
}

/// See [`Parser::boxed`].
///
/// Due to current implementation details, the inner value is not, in fact, a [`Box`], but is an [`Rc`](std::rc::Rc) to facilitate
/// efficient cloning. This is likely to change in the future. Unlike [`Box`], [`Rc`](std::rc::Rc) has no size guarantees: although
/// it is *currently* the same size as a raw pointer.
// TODO: Don't use an Rc
pub struct Boxed<'a, 'b, I: Input<'a>, O, E: ParserExtra<'a, I>> {
    inner: RefC<DynParser<'a, 'b, I, O, E>>,
}

impl<'a, 'b, I: Input<'a>, O, E: ParserExtra<'a, I>> Clone for Boxed<'a, 'b, I, O, E> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, 'b, I, O, E> ParserSealed<'a, I, O, E> for Boxed<'a, 'b, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        M::invoke(&*self.inner, inp)
    }

    fn boxed<'c>(self) -> Boxed<'a, 'c, I, O, E>
    where
        Self: MaybeSync + Sized + 'a + 'c,
    {
        // Never double-box parsers
        self
    }

    go_extra!(O);
}

impl<'a, I, O, E, T> ParserSealed<'a, I, O, E> for ::alloc::boxed::Box<T>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    T: Parser<'a, I, O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        T::go::<M>(self, inp)
    }

    go_extra!(O);
}

impl<'a, I, O, E, T> ParserSealed<'a, I, O, E> for ::alloc::rc::Rc<T>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    T: Parser<'a, I, O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        T::go::<M>(self, inp)
    }

    go_extra!(O);
}

impl<'a, I, O, E, T> ParserSealed<'a, I, O, E> for ::alloc::sync::Arc<T>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    T: Parser<'a, I, O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        T::go::<M>(self, inp)
    }

    go_extra!(O);
}

/// Create a parser that selects one or more input patterns and map them to an output value.
///
/// This is most useful when turning the tokens of a previous compilation pass (such as lexing) into data that can be
/// used for parsing, although it can also generally be used to select inputs and map them to outputs. Any unmapped
/// input patterns will become syntax errors, just as with [`Parser::filter`].
///
/// Internally, [`select!`] is very similar to a single-token [`Parser::filter`] and thinking of it as such might make
/// it less confusing.
///
/// `select!` requires that tokens implement [`Clone`] and the input type implements [`ValueInput`]. If you're trying
/// to access tokens referentially (for the sake of nested parsing, or simply because you want to avoid cloning the
/// token), see [`select_ref!`].
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
/// If you require access to the token's span or other metadata, you may add an argument after a pattern to gain access
/// to it (see the docs for [`Parser::map_with`] and [`MapExtra`]):
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
///     Token::Num(x) = e => Expr::Num(x).spanned(e.span()),
///     Token::Str(s) = e => Expr::Str(s).spanned(e.span()),
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
    ($($p:pat $(= $extra:ident)? $(if $guard:expr)? $(=> $out:expr)?),+ $(,)?) => ({
        $crate::primitive::select(
            move |x, extra| match (x, extra) {
                $(($p $(,$extra)?, ..) $(if $guard)? => ::core::option::Option::Some({ () $(;$out)? })),+,
                _ => ::core::option::Option::None,
            }
        )
    });
}

/// A version of [`select!`] that selects on token by reference instead of by value.
///
/// Useful if you want to extract elements from a token in a zero-copy manner.
///
/// See the docs for [`select!`] for more information.
///
/// Requires that the parser input implements [`BorrowInput`].
#[macro_export]
macro_rules! select_ref {
    ($($p:pat $(= $extra:ident)? $(if $guard:expr)? $(=> $out:expr)?),+ $(,)?) => ({
        $crate::primitive::select_ref(
            move |x, extra| match (x, extra) {
                $(($p $(,$extra)?, ..) $(if $guard)? => ::core::option::Option::Some({ () $(;$out)? })),+,
                _ => ::core::option::Option::None,
            }
        )
    });
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn zero_copy() {
        use crate::input::WithContext;
        use crate::prelude::*;

        #[derive(PartialEq, Debug)]
        enum Token<'a> {
            Ident(&'a str),
            String(&'a str),
        }

        type FileId = u32;
        type Span = SimpleSpan<usize, FileId>;

        fn parser<'a>() -> impl Parser<'a, WithContext<Span, &'a str>, [(Span, Token<'a>); 6]> {
            let ident = any()
                .filter(|c: &char| c.is_alphanumeric())
                .repeated()
                .at_least(1)
                .to_slice()
                .map(Token::Ident);

            let string = just('"')
                .then(any().filter(|c: &char| *c != '"').repeated())
                .then(just('"'))
                .to_slice()
                .map(Token::String);

            ident
                .or(string)
                .map_with(|token, e| (e.span(), token))
                .padded()
                .repeated()
                .collect_exactly()
        }

        assert_eq!(
            parser()
                .parse(r#"hello "world" these are "test" tokens"#.with_context(42))
                .into_result(),
            Ok([
                (Span::new(42, 0..5), Token::Ident("hello")),
                (Span::new(42, 6..13), Token::String("\"world\"")),
                (Span::new(42, 14..19), Token::Ident("these")),
                (Span::new(42, 20..23), Token::Ident("are")),
                (Span::new(42, 24..30), Token::String("\"test\"")),
                (Span::new(42, 31..37), Token::Ident("tokens")),
            ]),
        );
    }

    #[test]
    fn zero_copy_map_span() {
        use crate::input::MappedSpan;
        use crate::prelude::*;

        #[derive(PartialEq, Debug)]
        enum Token<'a> {
            Ident(&'a str),
            String(&'a str),
        }

        type FileId<'a> = &'a str;
        type Span<'a> = SimpleSpan<usize, FileId<'a>>;

        fn parser<'a, F: Fn(SimpleSpan) -> Span<'a> + 'a>(
        ) -> impl Parser<'a, MappedSpan<Span<'a>, &'a str, F>, [(Span<'a>, Token<'a>); 6]> {
            let ident = any()
                .filter(|c: &char| c.is_alphanumeric())
                .repeated()
                .at_least(1)
                .to_slice()
                .map(Token::Ident);

            let string = just('"')
                .then(any().filter(|c: &char| *c != '"').repeated())
                .then(just('"'))
                .to_slice()
                .map(Token::String);

            ident
                .or(string)
                .map_with(|token, e| (e.span(), token))
                .padded()
                .repeated()
                .collect_exactly()
        }

        let filename = "file.txt".to_string();
        let fstr = filename.as_str();

        assert_eq!(
            parser()
                .parse(
                    r#"hello "world" these are "test" tokens"#
                        .map_span(|span| Span::new(fstr, span.start()..span.end()))
                )
                .into_result(),
            Ok([
                (Span::new("file.txt", 0..5), Token::Ident("hello")),
                (Span::new("file.txt", 6..13), Token::String("\"world\"")),
                (Span::new("file.txt", 14..19), Token::Ident("these")),
                (Span::new("file.txt", 20..23), Token::Ident("are")),
                (Span::new("file.txt", 24..30), Token::String("\"test\"")),
                (Span::new("file.txt", 31..37), Token::Ident("tokens")),
            ]),
        );
    }

    #[test]
    fn zero_copy_repetition() {
        use crate::prelude::*;

        fn parser<'a>() -> impl Parser<'a, &'a str, Vec<u64>> {
            any()
                .filter(|c: &char| c.is_ascii_digit())
                .repeated()
                .at_least(1)
                .at_most(3)
                .to_slice()
                .map(|b: &str| b.parse::<u64>().unwrap())
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
        use crate::prelude::*;

        fn parser<'a>() -> impl Parser<'a, &'a str, (&'a str, u64, char)> {
            group((
                any()
                    .filter(|c: &char| c.is_ascii_alphabetic())
                    .repeated()
                    .at_least(1)
                    .to_slice()
                    .padded(),
                any()
                    .filter(|c: &char| c.is_ascii_digit())
                    .repeated()
                    .at_least(1)
                    .to_slice()
                    .map(|s: &str| s.parse::<u64>().unwrap())
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
        use crate::prelude::*;

        fn parser<'a>() -> impl Parser<'a, &'a str, [char; 3]> {
            group([just('a'), just('b'), just('c')])
        }

        assert_eq!(parser().parse("abc").into_result(), Ok(['a', 'b', 'c']));
        assert!(parser().parse("abd").has_errors());
    }

    #[test]
    fn unicode_str() {
        let input = "🄯🄚🹠🴎🄐🝋🰏🄂🬯🈦g🸵🍩🕔🈳2🬙🨞🅢🭳🎅h🵚🧿🏩🰬k🠡🀔🈆🝹🤟🉗🴟📵🰄🤿🝜🙘🹄5🠻🡉🱖🠓";
        let mut own = crate::input::InputOwn::<_, extra::Default>::new(input);
        let mut inp = own.as_ref_start();

        while let Some(_c) = inp.next() {}
    }

    #[test]
    fn iter() {
        use crate::prelude::*;

        fn parser<'a>() -> impl IterParser<'a, &'a str, char> {
            any().repeated()
        }

        let mut chars = String::new();
        for c in parser().parse_iter("abcdefg").into_result().unwrap() {
            chars.push(c);
        }

        assert_eq!(&chars, "abcdefg");
    }

    #[test]
    #[cfg(feature = "memoization")]
    fn exponential() {
        use crate::prelude::*;

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
                    .memoized()
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
        use crate::prelude::*;

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
                    .memoized();

                sum.or(atom)
            })
            .then_ignore(end())
        }

        assert_eq!(parser().parse("a+b+c").into_result().unwrap(), "abc");
    }

    #[cfg(debug_assertions)]
    mod debug_asserts {
        use crate::prelude::*;

        // TODO panic when left recursive parser is detected
        // #[test]
        // #[should_panic]
        // fn debug_assert_left_recursive() {
        //     recursive(|expr| {
        //         let atom = any::<&str, extra::Default>()
        //             .filter(|c: &char| c.is_alphabetic())
        //             .repeated()
        //             .at_least(1)
        //             .collect();

        //         let sum = expr
        //             .clone()
        //             .then_ignore(just('+'))
        //             .then(expr)
        //             .map(|(a, b)| format!("{}{}", a, b));

        //         sum.or(atom)
        //     })
        //     .then_ignore(end())
        //     .parse("a+b+c");
        // }

        #[test]
        #[should_panic]
        #[cfg(debug_assertions)]
        fn debug_assert_collect() {
            empty::<&str, extra::Default>()
                .to(())
                .repeated()
                .collect::<()>()
                .parse("a+b+c")
                .unwrap();
        }

        #[test]
        #[should_panic]
        #[cfg(debug_assertions)]
        fn debug_assert_separated_by() {
            empty::<&str, extra::Default>()
                .to(())
                .separated_by(empty())
                .collect::<()>()
                .parse("a+b+c");
        }

        #[test]
        fn debug_assert_separated_by2() {
            assert_eq!(
                empty::<&str, extra::Default>()
                    .to(())
                    .separated_by(just(','))
                    .count()
                    .parse(",")
                    .unwrap(),
                2
            );
        }

        #[test]
        #[should_panic]
        #[cfg(debug_assertions)]
        fn debug_assert_foldl() {
            assert_eq!(
                empty::<&str, extra::Default>()
                    .to(1)
                    .foldl(empty().repeated(), |n, ()| n + 1)
                    .parse("a+b+c")
                    .unwrap(),
                3
            );
        }

        #[test]
        #[should_panic]
        #[cfg(debug_assertions)]
        fn debug_assert_foldl_with() {
            let mut state = 100;
            empty::<&str, extra::Full<EmptyErr, i32, ()>>()
                .foldl_with(empty().to(()).repeated(), |_, _, _| ())
                .parse_with_state("a+b+c", &mut state);
        }

        #[test]
        #[should_panic]
        #[cfg(debug_assertions)]
        fn debug_assert_foldr() {
            empty::<&str, extra::Default>()
                .to(())
                .repeated()
                .foldr(empty(), |_, _| ())
                .parse("a+b+c");
        }

        #[test]
        #[should_panic]
        #[cfg(debug_assertions)]
        fn debug_assert_foldr_with_state() {
            empty::<&str, extra::Default>()
                .to(())
                .repeated()
                .foldr_with(empty(), |_, _, _| ())
                .parse_with_state("a+b+c", &mut ());
        }

        #[test]
        #[should_panic]
        #[cfg(debug_assertions)]
        fn debug_assert_repeated() {
            empty::<&str, extra::Default>()
                .to(())
                .repeated()
                .parse("a+b+c");
        }

        // TODO what about IterConfigure and TryIterConfigure?
    }

    #[test]
    #[should_panic]
    fn recursive_define_twice() {
        let mut expr = Recursive::declare();
        expr.define({
            let atom = any::<&str, extra::Default>()
                .filter(|c: &char| c.is_alphabetic())
                .repeated()
                .at_least(1)
                .collect();
            let sum = expr
                .clone()
                .then_ignore(just('+'))
                .then(expr.clone())
                .map(|(a, b)| format!("{}{}", a, b));

            sum.or(atom)
        });
        expr.define(expr.clone());

        expr.then_ignore(end()).parse("a+b+c");
    }

    #[test]
    #[should_panic]
    fn todo_err() {
        let expr = todo::<&str, String, extra::Default>();
        expr.then_ignore(end()).parse("a+b+c");
    }

    #[test]
    fn arc_impl() {
        use alloc::sync::Arc;

        fn parser<'a>() -> impl Parser<'a, &'a str, Vec<u64>> {
            Arc::new(
                any()
                    .filter(|c: &char| c.is_ascii_digit())
                    .repeated()
                    .at_least(1)
                    .at_most(3)
                    .to_slice()
                    .map(|b: &str| b.parse::<u64>().unwrap())
                    .padded()
                    .separated_by(just(',').padded())
                    .allow_trailing()
                    .collect()
                    .delimited_by(just('['), just(']')),
            )
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
    }

    #[test]
    fn box_impl() {
        fn parser<'a>() -> impl Parser<'a, &'a str, Vec<u64>> {
            Box::new(
                any()
                    .filter(|c: &char| c.is_ascii_digit())
                    .repeated()
                    .at_least(1)
                    .at_most(3)
                    .to_slice()
                    .map(|b: &str| b.parse::<u64>().unwrap())
                    .padded()
                    .separated_by(just(',').padded())
                    .allow_trailing()
                    .collect()
                    .delimited_by(just('['), just(']')),
            )
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
    }

    #[test]
    fn rc_impl() {
        use alloc::rc::Rc;

        fn parser<'a>() -> impl Parser<'a, &'a str, Vec<u64>> {
            Rc::new(
                any()
                    .filter(|c: &char| c.is_ascii_digit())
                    .repeated()
                    .at_least(1)
                    .at_most(3)
                    .to_slice()
                    .map(|b: &str| b.parse::<u64>().unwrap())
                    .padded()
                    .separated_by(just(',').padded())
                    .allow_trailing()
                    .collect()
                    .delimited_by(just('['), just(']')),
            )
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
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    struct MyErr(&'static str);

    impl<'a, I> crate::Error<'a, I> for MyErr
    where
        I: Input<'a>,
    {
        fn expected_found<E: IntoIterator<Item = Option<crate::MaybeRef<'a, I::Token>>>>(
            _expected: E,
            _found: Option<crate::MaybeRef<'a, I::Token>>,
            _span: I::Span,
        ) -> Self {
            MyErr("expected found")
        }

        fn merge(self, other: Self) -> Self {
            if self == MyErr("special") || other == MyErr("special") {
                MyErr("special")
            } else {
                self
            }
        }
    }

    #[test]
    fn err_prio_0() {
        #[allow(dead_code)]
        fn always_err<'a>() -> impl Parser<'a, &'a str, (), extra::Err<MyErr>> {
            empty().try_map(|_, _| Err(MyErr("special")))
        }

        assert_eq!(
            always_err().parse("test").into_result().unwrap_err(),
            vec![MyErr("special")]
        )
    }

    #[test]
    fn err_prio_1() {
        #[allow(dead_code)]
        fn always_err_choice<'a>() -> impl Parser<'a, &'a str, (), extra::Err<MyErr>> {
            choice((just("something").ignored(), empty())).try_map(|_, _| Err(MyErr("special")))
        }

        assert_eq!(
            always_err_choice().parse("test").into_result().unwrap_err(),
            vec![MyErr("special")]
        )
    }

    #[test]
    fn into_iter_no_error() {
        fn parser<'a>() -> impl Parser<'a, &'a str, (), extra::Err<MyErr>> {
            let many_as = just('a')
                .ignored()
                .repeated()
                .at_least(1)
                .collect::<Vec<_>>();

            many_as.into_iter().collect()
        }

        assert_eq!(parser().parse("aaa").into_result(), Ok(()));
    }

    #[cfg(feature = "nightly")]
    #[test]
    fn flatten() {
        fn parser<'a>() -> impl Parser<'a, &'a str, Vec<char>, extra::Err<MyErr>> {
            let many_as = just('a')
                .map(Some)
                .or(any().to(None))
                .repeated()
                .flatten()
                .collect::<Vec<_>>();

            many_as.into_iter().collect()
        }

        assert_eq!(
            parser().parse("abracadabra").into_result(),
            Ok(vec!['a', 'a', 'a', 'a', 'a'])
        );
    }

    #[test]
    #[cfg(feature = "unstable")]
    fn cached() {
        fn my_parser<'a>() -> impl Parser<'a, &'a str, &'a str, extra::Default> {
            any().repeated().exactly(5).to_slice()
        }

        struct MyCache;

        impl crate::cache::Cached for MyCache {
            type Parser<'src> = Boxed<'src, 'src, &'src str, &'src str, extra::Default>;

            fn make_parser<'src>(self) -> Self::Parser<'src> {
                Parser::boxed(my_parser())
            }
        }

        // usage < definition
        {
            let parser = crate::cache::Cache::new(MyCache);

            for _ in 0..2 {
                let s = "hello".to_string();

                assert_eq!(parser.get().parse(&s).into_result(), Ok("hello"));
                assert!(parser.get().parse("goodbye").into_result().is_err());
            }
        }

        // usage > definition
        {
            let s = "hello".to_string();

            for _ in 0..2 {
                let parser = crate::cache::Cache::new(MyCache);

                assert_eq!(parser.get().parse(&s).into_result(), Ok("hello"));
                assert!(parser.get().parse("goodbye").into_result().is_err());
            }
        }
    }

    #[test]
    #[allow(dead_code)]
    fn map_with_compiles() {
        enum Token {}
        enum Expr {}

        fn expr<'src, I>() -> impl Parser<'src, I, (Expr, SimpleSpan)> + 'src
        where
            I: Input<'src, Token = Token, Span = SimpleSpan> + 'src,
        {
            todo().map_with(|expr, e| (expr, e.span()))
        }
    }

    #[cfg(feature = "label")]
    #[test]
    fn label() {
        use crate::label::LabelError;

        fn parser<'src>() -> impl Parser<'src, &'src str, (), extra::Err<Rich<'src, char>>> {
            just("hello").labelled("greeting").as_context().ignored()
        }

        let mut err = <Rich<_> as crate::Error<&str>>::expected_found(
            Some(Some('h'.into())),
            Some('g'.into()),
            (0..1).into(),
        );
        <Rich<_, _, _> as LabelError<&str, _>>::label_with(&mut err, "greeting");
        assert_eq!(parser().parse("goodbye").into_errors(), vec![err]);

        let mut err = <Rich<_> as crate::Error<&str>>::expected_found(
            Some(Some('l'.into())),
            Some('p'.into()),
            (3..4).into(),
        );
        <Rich<_, _, _> as LabelError<&str, _>>::in_context(&mut err, "greeting", (0..3).into());
        assert_eq!(parser().parse("help").into_errors(), vec![err]);

        fn parser2<'src>() -> impl Parser<'src, &'src str, (), extra::Err<Rich<'src, char>>> {
            text::keyword("hello")
                .labelled("greeting")
                .as_context()
                .ignored()
        }

        let mut err = <Rich<_> as crate::Error<&str>>::expected_found(
            Some(Some('h'.into())),
            None,
            (0..7).into(),
        );
        <Rich<_, _, _> as LabelError<&str, _>>::label_with(&mut err, "greeting");
        assert_eq!(parser2().parse("goodbye").into_errors(), vec![err]);
    }
}
