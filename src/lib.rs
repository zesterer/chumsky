#![cfg_attr(feature = "nightly", feature(rustc_attrs))]
#![cfg_attr(not(any(doc, feature = "std")), no_std)]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(deprecated)] // TODO: Don't allow this

extern crate alloc;

pub mod chain;
pub mod combinator;
pub mod debug;
pub mod error;
pub mod primitive;
pub mod recovery;
pub mod recursive;
pub mod span;
pub mod stream;
pub mod text;

pub use crate::{error::Error, span::Span};

pub use crate::stream::{BoxStream, Flat, Stream};

use crate::{
    chain::Chain,
    combinator::*,
    debug::*,
    error::{merge_alts, Located},
    primitive::*,
    recovery::*,
};

use alloc::{boxed::Box, rc::Rc, string::String, sync::Arc, vec, vec::Vec};
use core::{
    cmp::Ordering,
    // TODO: Enable when stable
    //lazy::OnceCell,
    fmt,
    marker::PhantomData,
    ops::Range,
    panic::Location,
    str::FromStr,
};

#[cfg(doc)]
use std::{
    collections::HashMap,
    // TODO: Remove when switching to 2021 edition
    iter::FromIterator,
};

/// Commonly used functions, traits and types.
///
/// *Listen, three eyes,” he said, “don’t you try to outweird me, I get stranger things than you free with my breakfast
/// cereal.”*
pub mod prelude {
    pub use super::{
        error::{Error as _, Simple},
        primitive::{
            any, choice, empty, end, filter, filter_map, just, none_of, one_of, seq, take_until,
            todo,
        },
        recovery::{nested_delimiters, skip_parser, skip_then_retry_until, skip_until},
        recursive::{recursive, Recursive},
        select,
        span::Span as _,
        text,
        text::TextParser as _,
        BoxedParser, Parser,
    };
}

// TODO: Replace with `std::ops::ControlFlow` when stable
enum ControlFlow<C, B> {
    Continue(C),
    Break(B),
}

// ([], Ok((out, alt_err))) => parsing successful,
// alt_err = potential alternative error should a different number of optional patterns be parsed
// ([x, ...], Ok((out, alt_err)) => parsing failed, but recovery occurred so parsing may continue
// ([...], Err(err)) => parsing failed, recovery failed, and one or more errors were produced
// TODO: Change `alt_err` from `Option<Located<I, E>>` to `Vec<Located<I, E>>`
type PResult<I, O, E> = (
    Vec<Located<I, E>>,
    Result<(O, Option<Located<I, E>>), Located<I, E>>,
);

// Shorthand for a stream with the given input and error type.
type StreamOf<'a, I, E> = Stream<'a, I, <E as Error<I>>::Span>;

// [`Parser::parse_recovery`], but generic across the debugger.
fn parse_recovery_inner<
    'a,
    I: Clone,
    O,
    P: Parser<I, O>,
    D: Debugger,
    Iter: Iterator<Item = (I, <P::Error as Error<I>>::Span)> + 'a,
    S: Into<Stream<'a, I, <P::Error as Error<I>>::Span, Iter>>,
>(
    parser: &P,
    debugger: &mut D,
    stream: S,
) -> (Option<O>, Vec<P::Error>)
where
    P: Sized,
{
    #[allow(deprecated)]
    let (mut errors, res) = parser.parse_inner(debugger, &mut stream.into());
    let out = match res {
        Ok((out, _)) => Some(out),
        Err(err) => {
            errors.push(err);
            None
        }
    };
    (out, errors.into_iter().map(|e| e.error).collect())
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
#[allow(clippy::type_complexity)]
pub trait Parser<I: Clone, O> {
    /// The type of errors emitted by this parser.
    type Error: Error<I>; // TODO when default associated types are stable: = Cheap<I>;

    /// Parse a stream with all the bells & whistles. You can use this to implement your own parser combinators. Note
    /// that both the signature and semantic requirements of this function are very likely to change in later versions.
    /// Where possible, prefer more ergonomic combinators provided elsewhere in the crate rather than implementing your
    /// own. For example, [`custom`] provides a flexible, ergonomic way API for process input streams that likely
    /// covers your use-case.
    #[doc(hidden)]
    #[deprecated(
        note = "This method is excluded from the semver guarantees of chumsky. If you decide to use it, broken builds are your fault."
    )]
    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error>
    where
        Self: Sized;

    /// [`Parser::parse_inner`], but specialised for verbose output. Do not call this method directly.
    ///
    /// If you *really* need to implement this trait, this method should just directly invoke [`Parser::parse_inner`].
    #[doc(hidden)]
    #[deprecated(
        note = "This method is excluded from the semver guarantees of chumsky. If you decide to use it, broken builds are your fault."
    )]
    fn parse_inner_verbose(
        &self,
        d: &mut Verbose,
        s: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error>;

    /// [`Parser::parse_inner`], but specialised for silent output. Do not call this method directly.
    ///
    /// If you *really* need to implement this trait, this method should just directly invoke [`Parser::parse_inner`].
    #[doc(hidden)]
    #[deprecated(
        note = "This method is excluded from the semver guarantees of chumsky. If you decide to use it, broken builds are your fault."
    )]
    fn parse_inner_silent(
        &self,
        d: &mut Silent,
        s: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error>;

    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way.
    ///
    /// If `None` is returned (i.e: parsing failed) then there will *always* be at least one item in the error `Vec`.
    /// If you don't care about producing an output if errors are encountered, use [`Parser::parse`] instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// `&[I]`, a [`&str`], or a [`Stream`] to it.
    fn parse_recovery<'a, Iter, S>(&self, stream: S) -> (Option<O>, Vec<Self::Error>)
    where
        Self: Sized,
        Iter: Iterator<Item = (I, <Self::Error as Error<I>>::Span)> + 'a,
        S: Into<Stream<'a, I, <Self::Error as Error<I>>::Span, Iter>>,
    {
        parse_recovery_inner(self, &mut Silent::new(), stream)
    }

    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way. Unlike
    /// [`Parser::parse_recovery`], this function will produce verbose debugging output as it executes.
    ///
    /// If `None` is returned (i.e: parsing failed) then there will *always* be at least one item in the error `Vec`.
    /// If you don't care about producing an output if errors are encountered, use `Parser::parse` instead.
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// `&[I]`, a [`&str`], or a [`Stream`] to it.
    ///
    /// You'll probably want to make sure that this doesn't end up in production code: it exists only to help you debug
    /// your parser. Additionally, its API is quite likely to change in future versions.
    ///
    /// This method will receive more extensive documentation as the crate's debugging features mature.
    fn parse_recovery_verbose<'a, Iter, S>(&self, stream: S) -> (Option<O>, Vec<Self::Error>)
    where
        Self: Sized,
        Iter: Iterator<Item = (I, <Self::Error as Error<I>>::Span)> + 'a,
        S: Into<Stream<'a, I, <Self::Error as Error<I>>::Span, Iter>>,
    {
        let mut debugger = Verbose::new();
        let res = parse_recovery_inner(self, &mut debugger, stream);
        debugger.print();
        res
    }

    /// Parse a stream of tokens, yielding an output *or* any errors that were encountered along the way.
    ///
    /// If you wish to attempt to produce an output even if errors are encountered, use [`Parser::parse_recovery`].
    ///
    /// Although the signature of this function looks complicated, it's simpler than you think! You can pass a
    /// [`&[I]`], a [`&str`], or a [`Stream`] to it.
    fn parse<'a, Iter, S>(&self, stream: S) -> Result<O, Vec<Self::Error>>
    where
        Self: Sized,
        Iter: Iterator<Item = (I, <Self::Error as Error<I>>::Span)> + 'a,
        S: Into<Stream<'a, I, <Self::Error as Error<I>>::Span, Iter>>,
    {
        let (output, errors) = self.parse_recovery(stream);
        if errors.is_empty() {
            Ok(output.expect(
                "Parsing failed, but no errors were emitted. This is troubling, to say the least.",
            ))
        } else {
            Err(errors)
        }
    }

    /// Include this parser in the debugging output produced by [`Parser::parse_recovery_verbose`].
    ///
    /// You'll probably want to make sure that this doesn't end up in production code: it exists only to help you debug
    /// your parser. Additionally, its API is quite likely to change in future versions.
    /// Use this parser like a print statement, to display whatever you pass as the argument 'x'
    ///
    /// This method will receive more extensive documentation as the crate's debugging features mature.
    #[track_caller]
    fn debug<T>(self, x: T) -> Debug<Self>
    where
        Self: Sized,
        T: fmt::Display + 'static,
    {
        Debug(self, Rc::new(x), *core::panic::Location::caller())
    }

    /// Map the output of this parser to another value.
    ///
    /// The output type of this parser is `U`, the same as the function's output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// #[derive(Debug, PartialEq)]
    /// enum Token { Word(String), Num(u64) }
    ///
    /// let word = filter::<_, _, Cheap<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated().at_least(1)
    ///     .collect::<String>()
    ///     .map(Token::Word);
    ///
    /// let num = filter::<_, _, Cheap<char>>(|c: &char| c.is_ascii_digit())
    ///     .repeated().at_least(1)
    ///     .collect::<String>()
    ///     .map(|s| Token::Num(s.parse().unwrap()));
    ///
    /// let token = word.or(num);
    ///
    /// assert_eq!(token.parse("test"), Ok(Token::Word("test".to_string())));
    /// assert_eq!(token.parse("42"), Ok(Token::Num(42)));
    /// ```
    fn map<U, F>(self, f: F) -> Map<Self, F, O>
    where
        Self: Sized,
        F: Fn(O) -> U,
    {
        Map(self, f, PhantomData)
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
    fn map_with_span<U, F>(self, f: F) -> MapWithSpan<Self, F, O>
    where
        Self: Sized,
        F: Fn(O, <Self::Error as Error<I>>::Span) -> U,
    {
        MapWithSpan(self, f, PhantomData)
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
        F: Fn(Self::Error) -> Self::Error,
    {
        MapErr(self, f)
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
        F: Fn(Self::Error) -> Result<O, Self::Error>,
    {
        OrElse(self, f)
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
        F: Fn(Self::Error, <Self::Error as Error<I>>::Span) -> Self::Error,
    {
        MapErrWithSpan(self, f)
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
    fn try_map<U, F>(self, f: F) -> TryMap<Self, F, O>
    where
        Self: Sized,
        F: Fn(O, <Self::Error as Error<I>>::Span) -> Result<U, Self::Error>,
    {
        TryMap(self, f, PhantomData)
    }

    /// Validate an output, producing non-terminal errors if it does not fulfil certain criteria.
    ///
    /// This function also permits mapping the output to a value of another type, similar to [`Parser::map`].
    ///
    /// If you wish parsing of this pattern to halt when an error is generated instead of continuing, consider using
    /// [`Parser::try_map`] instead.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let large_int = text::int::<char, _>(10)
    ///     .from_str()
    ///     .unwrapped()
    ///     .validate(|x: u32, span, emit| {
    ///         if x < 256 { emit(Simple::custom(span, format!("{} must be 256 or higher.", x))) }
    ///         x
    ///     });
    ///
    /// assert_eq!(large_int.parse("537"), Ok(537));
    /// assert!(large_int.parse("243").is_err());
    /// ```
    fn validate<F, U>(self, f: F) -> Validate<Self, O, F>
    where
        Self: Sized,
        F: Fn(O, <Self::Error as Error<I>>::Span, &mut dyn FnMut(Self::Error)) -> U,
    {
        Validate(self, f, PhantomData)
    }

    /// Label the pattern parsed by this parser for more useful error messages.
    ///
    /// This is useful when you want to give users a more useful description of an expected pattern than simply a list
    /// of possible initial tokens. For example, it's common to use the term "expression" at a catch-all for a number
    /// of different constructs in many languages.
    ///
    /// This does not label recovered errors generated by sub-patterns within the parser, only error *directly* emitted
    /// by the parser.
    ///
    /// This does not label errors where the labelled pattern consumed input (i.e: in unambiguous cases).
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// *Note: There is a chance that this method will be deprecated in favour of a more general solution in later
    /// versions of the crate.*
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    /// let frac = text::digits(10)
    ///     .chain(just('.'))
    ///     .chain::<char, _, _>(text::digits(10))
    ///     .collect::<String>()
    ///     .then_ignore(end())
    ///     .labelled("number");
    ///
    /// assert_eq!(frac.parse("42.3"), Ok("42.3".to_string()));
    /// assert_eq!(frac.parse("hello"), Err(vec![Cheap::expected_input_found(0..1, Vec::new(), Some('h')).with_label("number")]));
    /// assert_eq!(frac.parse("42!"), Err(vec![Cheap::expected_input_found(2..3, vec![Some('.')], Some('!')).with_label("number")]));
    /// ```
    fn labelled<L>(self, label: L) -> Label<Self, L>
    where
        Self: Sized,
        L: Into<<Self::Error as Error<I>>::Label> + Clone,
    {
        Label(self, label)
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
    fn to<U>(self, x: U) -> To<Self, O, U>
    where
        Self: Sized,
        U: Clone,
    {
        To(self, x, PhantomData)
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
    fn foldl<A, B, F>(self, f: F) -> Foldl<Self, F, A, B>
    where
        Self: Parser<I, (A, B)> + Sized,
        B: IntoIterator,
        F: Fn(A, B::Item) -> A,
    {
        Foldl(self, f, PhantomData)
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
    fn foldr<'a, A, B, F>(self, f: F) -> Foldr<Self, F, A, B>
    where
        Self: Parser<I, (A, B)> + Sized,
        A: IntoIterator,
        A::IntoIter: DoubleEndedIterator,
        F: Fn(A::Item, B) -> B + 'a,
    {
        Foldr(self, f, PhantomData)
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
        To(self, (), PhantomData)
    }

    /// Collect the output of this parser into a type implementing [`FromIterator`].
    ///
    /// This is commonly useful for collecting [`Vec<char>`] outputs into [`String`]s, or [`(T, U)`] into a
    /// [`HashMap`] and is analogous to [`Iterator::collect`].
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
    fn collect<C>(self) -> Map<Self, fn(O) -> C, O>
    where
        Self: Sized,
        O: IntoIterator,
        C: core::iter::FromIterator<O::Item>,
    {
        self.map(|items| C::from_iter(items.into_iter()))
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
    fn then<U, P>(self, other: P) -> Then<Self, P>
    where
        Self: Sized,
        P: Parser<I, U, Error = Self::Error>,
    {
        Then(self, other)
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
    fn then_with<U, P, F: Fn(O) -> P>(self, other: F) -> ThenWith<I, O, U, Self, P, F>
    where
        Self: Sized,
        P: Parser<I, U, Error = Self::Error>,
    {
        ThenWith(self, other, PhantomData)
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
    fn chain<T, U, P>(self, other: P) -> Map<Then<Self, P>, fn((O, U)) -> Vec<T>, (O, U)>
    where
        Self: Sized,
        U: Chain<T>,
        O: Chain<T>,
        P: Parser<I, U, Error = Self::Error>,
    {
        self.then(other).map(|(a, b)| {
            let mut v = Vec::with_capacity(a.len() + b.len());
            a.append_to(&mut v);
            b.append_to(&mut v);
            v
        })
    }

    /// Flatten a nested collection.
    ///
    /// This use-cases of this method are broadly similar to those of [`Iterator::flatten`].
    ///
    /// The output type of this parser is `Vec<T>`, where the original parser output was
    /// `impl IntoIterator<Item = impl IntoIterator<Item = T>>`.
    fn flatten<T, Inner>(self) -> Map<Self, fn(O) -> Vec<T>, O>
    where
        Self: Sized,
        O: IntoIterator<Item = Inner>,
        Inner: IntoIterator<Item = T>,
    {
        self.map(|xs| xs.into_iter().flat_map(|xs| xs.into_iter()).collect())
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
    fn ignore_then<U, P>(self, other: P) -> IgnoreThen<Self, P, O, U>
    where
        Self: Sized,
        P: Parser<I, U, Error = Self::Error>,
    {
        Map(Then(self, other), |(_, u)| u, PhantomData)
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
    fn then_ignore<U, P>(self, other: P) -> ThenIgnore<Self, P, O, U>
    where
        Self: Sized,
        P: Parser<I, U, Error = Self::Error>,
    {
        Map(Then(self, other), |(o, _)| o, PhantomData)
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
    fn padded_by<U, P>(self, other: P) -> ThenIgnore<IgnoreThen<P, Self, U, O>, P, O, U>
    where
        Self: Sized,
        P: Parser<I, U, Error = Self::Error> + Clone,
    {
        other.clone().ignore_then(self).then_ignore(other)
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
    fn delimited_by<U, V, L, R>(self, start: L, end: R) -> DelimitedBy<Self, L, R, U, V>
    where
        Self: Sized,
        L: Parser<I, U, Error = Self::Error>,
        R: Parser<I, V, Error = Self::Error>,
    {
        DelimitedBy {
            item: self,
            start,
            end,
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
    fn or<P>(self, other: P) -> Or<Self, P>
    where
        Self: Sized,
        P: Parser<I, O, Error = Self::Error>,
    {
        Or(self, other)
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
    fn recover_with<S>(self, strategy: S) -> Recovery<Self, S>
    where
        Self: Sized,
        S: Strategy<I, O, Self::Error>,
    {
        Recovery(self, strategy)
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
        OrNot(self)
    }

    /// Parses a single token if, and only if, the pattern fails to parse.
    ///
    /// The output type of this parser is `I`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Tree {
    ///     Text(String),
    ///     Group(Vec<Self>),
    /// }
    ///
    /// // Arbitrary text, nested in a tree with { ... } delimiters
    /// let tree = recursive::<_, _, _, _, Cheap<char>>(|tree| {
    ///     let text = one_of("{}")
    ///         .not()
    ///         .repeated()
    ///         .at_least(1)
    ///         .collect()
    ///         .map(Tree::Text);
    ///
    ///     let group = tree
    ///         .repeated()
    ///         .delimited_by(just('{'), just('}'))
    ///         .map(Tree::Group);
    ///
    ///     text.or(group)
    /// });
    ///
    /// assert_eq!(
    ///     tree.parse("{abcd{efg{hijk}lmn{opq}rs}tuvwxyz}"),
    ///     Ok(Tree::Group(vec![
    ///         Tree::Text("abcd".to_string()),
    ///         Tree::Group(vec![
    ///             Tree::Text("efg".to_string()),
    ///             Tree::Group(vec![
    ///                 Tree::Text("hijk".to_string()),
    ///             ]),
    ///             Tree::Text("lmn".to_string()),
    ///             Tree::Group(vec![
    ///                 Tree::Text("opq".to_string()),
    ///             ]),
    ///             Tree::Text("rs".to_string()),
    ///         ]),
    ///         Tree::Text("tuvwxyz".to_string()),
    ///     ])),
    /// );
    /// ```
    fn not(self) -> Not<Self, O>
    where
        Self: Sized,
    {
        Not(self, PhantomData)
    }

    /// Parse a pattern any number of times (including zero times).
    ///
    /// Input is eagerly parsed. Be aware that the parser will accept no occurrences of the pattern too. Consider using
    /// [`Repeated::at_least`] instead if it better suits your use-case.
    ///
    /// The output type of this parser is `Vec<O>`.
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
    fn repeated(self) -> Repeated<Self>
    where
        Self: Sized,
    {
        Repeated(self, 0, None)
    }

    /// Parse a pattern, separated by another, any number of times.
    ///
    /// You can use [`SeparatedBy::allow_leading`] or [`SeparatedBy::allow_trailing`] to allow leading or trailing
    /// separators.
    ///
    /// The output type of this parser is `Vec<O>`.
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
    fn separated_by<U, P>(self, other: P) -> SeparatedBy<Self, P, U>
    where
        Self: Sized,
        P: Parser<I, U, Error = Self::Error>,
    {
        SeparatedBy {
            item: self,
            delimiter: other,
            at_least: 0,
            at_most: None,
            allow_leading: false,
            allow_trailing: false,
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
        Rewind(self)
    }

    /// Box the parser, yielding a parser that performs parsing through dynamic dispatch.
    ///
    /// Boxing a parser might be useful for:
    ///
    /// - Dynamically building up parsers at runtime
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
    fn boxed<'a>(self) -> BoxedParser<'a, I, O, Self::Error>
    where
        Self: Sized + 'a,
    {
        BoxedParser(Rc::new(self))
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
    fn from_str<U>(self) -> Map<Self, fn(O) -> Result<U, U::Err>, O>
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
    #[track_caller]
    fn unwrapped<U, E>(self) -> Unwrapped<Self, E, <Self as Parser<I, O>>::Error>
    where
        Self: Sized + Parser<I, Result<U, E>>,
        E: fmt::Debug,
    {
        Unwrapped(Location::caller(), self, PhantomData)
    }
}

impl<'a, I: Clone, O, T: Parser<I, O> + ?Sized> Parser<I, O> for &'a T {
    type Error = T::Error;

    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        debugger.invoke::<_, _, T>(*self, stream)
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

impl<I: Clone, O, T: Parser<I, O> + ?Sized> Parser<I, O> for Box<T> {
    type Error = T::Error;

    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        debugger.invoke::<_, _, T>(&*self, stream)
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

impl<I: Clone, O, T: Parser<I, O> + ?Sized> Parser<I, O> for Rc<T> {
    type Error = T::Error;

    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        debugger.invoke::<_, _, T>(&*self, stream)
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

impl<I: Clone, O, T: Parser<I, O> + ?Sized> Parser<I, O> for Arc<T> {
    type Error = T::Error;

    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        debugger.invoke::<_, _, T>(&*self, stream)
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

/// See [`Parser::boxed`].
///
/// This type is a [`repr(transparent)`](https://doc.rust-lang.org/nomicon/other-reprs.html#reprtransparent) wrapper
/// around its inner value.
///
/// Due to current implementation details, the inner value is not, in fact, a [`Box`], but is an [`Rc`] to facilitate
/// efficient cloning. This is likely to change in the future. Unlike [`Box`], [`Rc`] has no size guarantees: although
/// it is *currently* the same size as a raw pointer.
// TODO: Don't use an Rc
#[must_use]
#[repr(transparent)]
pub struct BoxedParser<'a, I, O, E: Error<I>>(Rc<dyn Parser<I, O, Error = E> + 'a>);

impl<'a, I, O, E: Error<I>> Clone for BoxedParser<'a, I, O, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<'a, I: Clone, O, E: Error<I>> Parser<I, O> for BoxedParser<'a, I, O, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        #[allow(deprecated)]
        debugger.invoke(&self.0, stream)
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

    fn boxed<'b>(self) -> BoxedParser<'b, I, O, Self::Error>
    where
        Self: Sized + 'b,
    {
        // Avoid boxing twice.
        self
    }
}

/// Create a parser that selects one or more input patterns and map them to an output value.
///
/// This is most useful when turning the tokens of a previous compilation pass (such as lexing) into data that can be
/// used for parsing, although it can also generally be used to select inputs and map them to outputs. Any unmapped
/// input patterns will become syntax errors, just as with [`filter`].
///
/// The macro is semantically similar to a `match` expression and so supports
/// [pattern guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards) too.
///
/// ```ignore
/// select! {
///     Token::Bool(x) if x => Expr::True,
///     Token::Bool(x) if !x => Expr::False,
/// }
/// ```
///
/// If you require access to the input's span, you may add an argument before the patterns to gain access to it.
///
/// ```ignore
/// select! { |span|
///     Token::Num(x) => Expr::Num(x).spanned(span),
///     Token::Str(s) => Expr::Str(s).spanned(span),
/// }
/// ```
///
/// Internally, [`select!`] is a loose wrapper around [`filter_map`] and thinking of it as such might make it less
/// confusing.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Cheap};
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
/// let ast = recursive::<_, _, _, _, Cheap<Token>>(|ast| {
///     let literal = select! {
///         Token::Num(x) => Ast::Num(x),
///         Token::Bool(x) => Ast::Bool(x),
///     };
///
///     literal.or(ast
///         .repeated()
///         .delimited_by(just(Token::LParen), just(Token::RParen))
///         .map(Ast::List))
/// });
///
/// use Token::*;
/// assert_eq!(
///     ast.parse(vec![LParen, Num(5), LParen, Bool(false), Num(42), RParen, RParen]),
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
    (|$span:ident| $($p:pat $(if $guard:expr)? => $out:expr),+ $(,)?) => ({
        $crate::primitive::filter_map(move |$span, x| match x {
            $($p $(if $guard)? => ::core::result::Result::Ok($out)),+,
            _ => ::core::result::Result::Err($crate::error::Error::expected_input_found($span, ::core::option::Option::None, ::core::option::Option::Some(x))),
        })
    });

    ($($p:pat $(if $guard:expr)? => $out:expr),+ $(,)?) => (select!(|_span| $($p $(if $guard)? => $out),+));
}
