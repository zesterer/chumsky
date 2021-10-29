#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(deprecated)] // TODO: Don't allow this
// TODO: Enable when stable
//#![feature(once_cell)]

/// Utilities for debugging parsers.
pub mod debug;
/// Combinators that allow combining and extending existing parsers.
pub mod combinator;
/// Error types, traits and utilities.
pub mod error;
/// Traits that allow chaining parser outputs together.
pub mod chain;
/// Parser primitives that accept specific token patterns.
pub mod primitive;
/// Types and traits that facilitate error recovery.
pub mod recovery;
/// Recursive parsers (parser that include themselves within their patterns).
pub mod recursive;
/// Types and traits related to spans.
pub mod span;
/// Token streams and behaviours.
pub mod stream;
/// Text-specific parsers and utilities.
pub mod text;

pub use crate::{
    error::Error,
    span::Span,
};

pub use crate::{
    stream::{Stream, BoxStream, Flat},
};

use crate::{
    chain::Chain,
    combinator::*,
    primitive::*,
    recovery::*,
    debug::*,
};

use std::{
    marker::PhantomData,
    rc::Rc,
    cmp::Ordering,
    ops::Range,
    // TODO: Enable when stable
    //lazy::OnceCell,
    fmt,
};

/// Commonly used functions, traits and types.
pub mod prelude {
    pub use super::{
        error::{Error as _, Simple},
        text::TextParser as _,
        span::Span as _,
        primitive::{any, end, filter, filter_map, just, one_of, none_of, seq},
        recovery::{skip_then_retry_until, nested_delimiters},
        recursive::recursive,
        text,
        Parser,
        BoxedParser,
    };
}

// TODO: Replace with `std::ops::ControlFlow` when stable
enum ControlFlow<C, B> {
    Continue(C),
    Break(B),
}

/// An internal type used to facilitate error prioritisation. You shouldn't need to interact with this type during
/// normal use of the crate.
pub struct Located<I, E> {
    at: usize,
    error: E,
    phantom: PhantomData<I>,
}

impl<I, E: Error<I>> Located<I, E> {
    /// Create a new [`Located`] with the give input position and error.
    pub fn at(at: usize, error: E) -> Self {
        Self { at, error, phantom: PhantomData }
    }

    /// Get the maximum of two located errors. If they hold the same position in the input, merge them.
    pub fn max(self, other: impl Into<Option<Self>>) -> Self {
        let other = match other.into() {
            Some(other) => other,
            None => return self,
        };
        match self.at.cmp(&other.at) {
            Ordering::Greater => self,
            Ordering::Less => other,
            Ordering::Equal => Self {
                error: self.error.merge(other.error),
                ..self
            },
        }
    }

    /// Map the error with the given function.
    pub fn map<U, F: FnOnce(E) -> U>(self, f: F) -> Located<I, U> {
        Located {
            at: self.at,
            error: f(self.error),
            phantom: PhantomData,
        }
    }
}

// Merge two alternative errors
// TODO: Allow multiple alternative errors
fn merge_alts<I, E: Error<I>>(a: Option<Located<I, E>>, b: Option<Located<I, E>>) -> Option<Located<I, E>> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.max(b)),
        (a, b) => a.or(b),
    }
}

// ([], Ok((out, recovered, alt_err))) => parsing successful, recovered = whether the false is a false recovered value,
// alt_err = potential alternative error should a different number of optional patterns be parsed
// ([x, ...], Ok(out)) => parsing failed, but recovery occurred so parsing may continue
// ([...], Err(err)) => parsing failed, recovery failed, and one or more errors were produced
// TODO: Change `alt_err` from `Option<Located<I, E>>` to `Vec<Located<I, E>>`
type PResult<I, O, E> = (Vec<Located<I, E>>, Result<(O, Option<Located<I, E>>), Located<I, E>>);

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
>(parser: &P, debugger: &mut D, stream: S) -> (Option<O>, Vec<P::Error>) where P: Sized {
    #[allow(deprecated)]
    let (mut errors, res) = parser.parse_inner(debugger, &mut stream.into());
    let out = match res {
        Ok((out, _)) => Some(out),
        Err(err) => {
            errors.push(err);
            None
        },
    };
    (out, errors.into_iter().map(|e| e.error).collect())
}

/// A trait implemented by parsers.
///
/// Parsers take a stream of tokens of type `I` and attempt to parse them into a value of type `O`. In doing so, they
/// may encounter errors. These need not be fatal to the parsing process: syntactic errors can be recovered from and a
/// valid output may still be generated alongside any syntax errors that were encountered along the way. Usually, this
/// output comes in the form of an [Abstract Syntax Tree](https://en.wikipedia.org/wiki/Abstract_syntax_tree) (AST).
pub trait Parser<I: Clone, O> {
    /// The type of errors emitted by this parser.
    type Error: Error<I>; // TODO when default associated types are stable: = Cheap<I>;

    /// Parse a stream with all the bells & whistles. You can use this to implement your own parser combinators. Note
    /// that both the signature and semantic requirements of this function are very likely to change in later versions.
    /// Where possible, prefer more ergonomic combinators provided elsewhere in the crate rather than implementing your
    /// own. For example, [`custom`] provides a flexible, ergonomic way API for process input streams that likely
    /// covers your use-case.
    #[deprecated(note = "This method is excluded from the semver guarantees of chumsky. If you decide to use it, broken builds are your fault.")]
    fn parse_inner<D: Debugger>(&self, debugger: &mut D, stream: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> where Self: Sized;

    /// [`Parser::parse_inner`], but specialised for verbose output. Do not call this method directly.
    ///
    /// If you *really* need to implement this trait, this method should just directly invoke [`Parser::parse_inner`].
    #[deprecated(note = "This method is excluded from the semver guarantees of chumsky. If you decide to use it, broken builds are your fault.")]
    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error>;

    /// [`Parser::parse_inner`], but specialised for silent output. Do not call this method directly.
    ///
    /// If you *really* need to implement this trait, this method should just directly invoke [`Parser::parse_inner`].
    #[deprecated(note = "This method is excluded from the semver guarantees of chumsky. If you decide to use it, broken builds are your fault.")]
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error>;

    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way.
    ///
    /// If you don't care about producing an output if errors are encountered, use `Parser::parse` instead.
    fn parse_recovery<
        'a,
        Iter: Iterator<Item = (I, <Self::Error as Error<I>>::Span)> + 'a,
        S: Into<Stream<'a, I, <Self::Error as Error<I>>::Span, Iter>>,
    >(&self, stream: S) -> (Option<O>, Vec<Self::Error>) where Self: Sized {
        parse_recovery_inner(self, &mut Silent::new(), stream)
    }

    /// Parse a stream of tokens, yielding an output if possible, and any errors encountered along the way. Unlike
    /// [`Parser::parse_recovery`], this function will produce verbose debugging output as it executes.
    ///
    /// If you don't care about producing an output if errors are encountered, use `Parser::parse` instead.
    ///
    /// You'll probably want to make sure that this doesn't end up in production code: it exists only to help you debug
    /// your parser. Additionally, its API is quite likely to change in future versions.
    fn parse_recovery_verbose<
        'a,
        Iter: Iterator<Item = (I, <Self::Error as Error<I>>::Span)> + 'a,
        S: Into<Stream<'a, I, <Self::Error as Error<I>>::Span, Iter>>,
    >(&self, stream: S) -> (Option<O>, Vec<Self::Error>) where Self: Sized {
        let mut debugger = Verbose::new();
        let res = parse_recovery_inner(self, &mut debugger, stream);
        debugger.print();
        res
    }

    /// Parse a stream of tokens, yielding an output *or* any errors that were encountered along the way.
    ///
    /// If you wish to attempt to produce an output even if errors are encountered, use [`Parser::parse_recovery`].
    fn parse<
        'a,
        Iter: Iterator<Item = (I, <Self::Error as Error<I>>::Span)> + 'a,
        S: Into<Stream<'a, I, <Self::Error as Error<I>>::Span, Iter>>,
    >(&self, stream: S) -> Result<O, Vec<Self::Error>> where Self: Sized {
        let (output, errors) = self.parse_recovery(stream);
        if errors.is_empty() {
            Ok(output.expect("Parsing failed, but no errors were emitted. This is troubling, to say the least."))
        } else {
            Err(errors)
        }
    }

    /// Include this parser in the debugging output produced by [`Parser::parse_recovery_verbose`].
    ///
    /// You'll probably want to make sure that this doesn't end up in production code: it exists only to help you debug
    /// your parser. Additionally, its API is quite likely to change in future versions.
    #[track_caller]
    fn debug<T: fmt::Display + 'static>(self, x: T) -> Debug<Self> where Self: Sized {
        Debug(self, Rc::new(x), *std::panic::Location::caller())
    }

    /// Map the output of this parser to another value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
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
    fn map<U, F: Fn(O) -> U>(self, f: F) -> Map<Self, F, O> where Self: Sized { Map(self, f, PhantomData) }

    /// Map the output of this parser to another value, making use of the pattern's overall span.
    ///
    /// This is very useful when generating an AST that attaches a span to each AST node.
    fn map_with_span<U, F: Fn(O, <Self::Error as Error<I>>::Span) -> U>(self, f: F) -> MapWithSpan<Self, F, O>
        where Self: Sized
    { MapWithSpan(self, f, PhantomData) }

    /// Map the primary error of this parser to another value.
    ///
    /// This function is most useful when using a custom error type, allowing you to augment errors according to
    /// context.
    fn map_err<F: Fn(Self::Error) -> Self::Error>(self, f: F) -> MapErr<Self, F>
        where Self: Sized
    { MapErr(self, f) }

    /// After a successful parse, apply a fallible function to the output. If the function produces an error, treat it
    /// as a parsing error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let byte = text::int::<_, Simple<char>>(10)
    ///     .try_map(|s, span| s
    ///         .parse::<u8>()
    ///         .map_err(|e| Simple::custom(span, format!("{}", e))));
    ///
    /// assert!(byte.parse("255").is_ok());
    /// assert!(byte.parse("256").is_err()); // Out of range
    /// ```
    fn try_map<U, F: Fn(O, <Self::Error as Error<I>>::Span) -> Result<U, Self::Error>>(self, f: F) -> TryMap<Self, F, O>
        where Self: Sized
    { TryMap(self, f, PhantomData) }

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
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let frac = text::digits(10)
    ///     .chain(just('.'))
    ///     .chain::<char, _, _>(text::digits(10))
    ///     .collect::<String>()
    ///     .then_ignore(end())
    ///     .labelled("number");
    ///
    /// assert_eq!(frac.parse("42.3"), Ok("42.3".to_string()));
    /// assert_eq!(frac.parse("hello"), Err(vec![Cheap::expected_input_found(0..1, None, Some('h')).with_label("number")]));
    /// assert_eq!(frac.parse("42!"), Err(vec![Cheap::expected_input_found(2..3, Some('.'), Some('!')).with_label("number")]));
    /// ```
    fn labelled<L: Into<<Self::Error as Error<I>>::Label> + Clone>(self, label: L) -> Label<Self, L>
        where Self: Sized
    { Label(self, label) }

    /// Transform all outputs of this parser to a pretermined value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// enum Op { Add, Sub, Mul, Div }
    ///
    /// let op = just::<_, Cheap<char>>('+').to(Op::Add)
    ///     .or(just('-').to(Op::Sub))
    ///     .or(just('*').to(Op::Mul))
    ///     .or(just('/').to(Op::Div));
    ///
    /// assert_eq!(op.parse("+"), Ok(Op::Add));
    /// assert_eq!(op.parse("/"), Ok(Op::Div));
    /// ```
    fn to<U: Clone>(self, x: U) -> To<Self, O, U> where Self: Sized { To(self, x, PhantomData) }

    /// Left-fold the output of the parser into a single value.
    ///
    /// The output of the original parser must be of type `(A, impl IntoIterator<Item = B>)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let int = text::int::<char, Cheap<char>>(10)
    ///     .map(|s| s.parse().unwrap());
    ///
    /// let sum = int
    ///     .then(just('+').ignore_then(int).repeated())
    ///     .foldl(|a, b| a + b);
    ///
    /// assert_eq!(sum.parse("1+12+3+9"), Ok(25));
    /// assert_eq!(sum.parse("6"), Ok(6));
    /// ```
    fn foldl<A, B, F: Fn(A, B::Item) -> A>(self, f: F) -> Foldl<Self, F, A, B>
    where
        Self: Parser<I, (A, B)> + Sized,
        B: IntoIterator,
    { Foldl(self, f, PhantomData) }

    /// Right-fold the output of the parser into a single value.
    ///
    /// The output of the original parser must be of type `(impl IntoIterator<Item = A>, B)`. Because right-folds work
    /// backwards, the iterator must implement [`DoubleEndedIterator`] so that it can be reversed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let int = text::int::<char, Cheap<char>>(10)
    ///     .map(|s| s.parse().unwrap());
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
    fn foldr<'a, A, B, F: Fn(A::Item, B) -> B + 'a>(self, f: F) -> Foldr<Self, F, A, B>
    where
        Self: Parser<I, (A, B)> + Sized,
        A: IntoIterator,
        A::IntoIter: DoubleEndedIterator,
    { Foldr(self, f, PhantomData) }

    /// Ignore the output of this parser, yielding `()` as an output instead.
    ///
    /// This can be used to reduce the cost of parsing by avoiding unnecessary allocations (most collections containing
    /// [ZSTs](https://doc.rust-lang.org/nomicon/exotic-sizes.html#zero-sized-types-zsts)
    /// [do not allocate](https://doc.rust-lang.org/std/vec/struct.Vec.html#guarantees)). For example, it's common to
    /// want to ignore whitespace in many grammars (see [`text::whitespace`]).
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// // A parser that parses any number of whitespace characters without allocating
    /// let whitespace = filter::<_, _, Cheap<char>>(|c: &char| c.is_whitespace())
    ///     .ignored()
    ///     .repeated();
    ///
    /// assert_eq!(whitespace.parse("    "), Ok(vec![(); 4]));
    /// assert_eq!(whitespace.parse("  hello"), Ok(vec![(); 2]));
    /// ```
    fn ignored(self) -> Ignored<Self, O> where Self: Sized { To(self, (), PhantomData) }

    /// Collect the output of this parser into a type implementing [`FromIterator`].
    ///
    /// This is commonly useful for collecting [`Vec<char>`] outputs into [`String`]s, or [`(T, U)`] into a
    /// [`HashMap`] and is analagous to [`Iterator::collect`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let word = filter::<_, _, Cheap<char>>(|c: &char| c.is_alphabetic()) // This parser produces an output of `char`
    ///     .repeated() // This parser produces an output of `Vec<char>`
    ///     .collect::<String>(); // But `Vec<char>` is less useful than `String`, so convert to the latter
    ///
    /// assert_eq!(word.parse("hello"), Ok("hello".to_string()));
    /// ```
    // TODO: Make `Parser::repeated` generic over an `impl FromIterator` to reduce required allocations
    fn collect<C: core::iter::FromIterator<O::Item>>(self) -> Map<Self, fn(O) -> C, O>
        where Self: Sized, O: IntoIterator
    { self.map(|items| C::from_iter(items.into_iter())) }

    /// Parse one thing and then another thing, yielding a tuple of the two outputs.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let word = filter::<_, _, Cheap<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated().at_least(1)
    ///     .collect::<String>();
    /// let two_words = word.then_ignore(just(' ')).then(word);
    ///
    /// assert_eq!(two_words.parse("dog cat"), Ok(("dog".to_string(), "cat".to_string())));
    /// assert!(two_words.parse("hedgehog").is_err());
    /// ```
    fn then<U, P: Parser<I, U>>(self, other: P) -> Then<Self, P> where Self: Sized { Then(self, other) }

    /// Parse one thing and then another thing, attempting to chain the two outputs into a [`Vec`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let int = just('-').or_not()
    ///     .chain(filter::<_, _, Cheap<char>>(|c: &char| c.is_ascii_digit() && *c != '0')
    ///         .chain(filter::<_, _, Cheap<char>>(|c: &char| c.is_ascii_digit()).repeated()))
    ///     .or(just('0').map(|c| vec![c]))
    ///     .then_ignore(end())
    ///     .collect::<String>()
    ///     .map(|s| s.parse().unwrap());
    ///
    /// assert_eq!(int.parse("0"), Ok(0));
    /// assert_eq!(int.parse("415"), Ok(415));
    /// assert_eq!(int.parse("-50"), Ok(-50));
    /// assert!(int.parse("-0").is_err());
    /// assert!(int.parse("05").is_err());
    /// ```
    fn chain<T, U, P: Parser<I, U, Error = Self::Error>>(self, other: P) -> Map<Then<Self, P>, fn((O, U)) -> Vec<T>, (O, U)>
    where
        Self: Sized,
        U: Chain<T>,
        O: Chain<T>,
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
    fn flatten<T, Inner>(self) -> Map<Self, fn(O) -> Vec<T>, O>
    where
        Self: Sized,
        O: IntoIterator<Item = Inner>,
        Inner: IntoIterator<Item = T>,
    { self.map(|xs| xs.into_iter().map(|xs| xs.into_iter()).flatten().collect()) }

    /// Parse one thing and then another thing, yielding only the output of the latter.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let zeroes = filter::<_, _, Cheap<char>>(|c: &char| *c == '0').ignored().repeated();
    /// let digits = filter(|c: &char| c.is_ascii_digit()).repeated();
    /// let integer = zeroes
    ///     .ignore_then(digits)
    ///     .collect::<String>()
    ///     .map(|s| s.parse().unwrap());
    ///
    /// assert_eq!(integer.parse("00064"), Ok(64));
    /// assert_eq!(integer.parse("32"), Ok(32));
    /// ```
    fn ignore_then<U, P: Parser<I, U>>(self, other: P) -> IgnoreThen<Self, P, O, U>
        where Self: Sized
    { Map(Then(self, other), |(_, u)| u, PhantomData) }

    /// Parse one thing and then another thing, yielding only the output of the former.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
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
    fn then_ignore<U, P: Parser<I, U>>(self, other: P) -> ThenIgnore<Self, P, O, U>
        where Self: Sized
    { Map(Then(self, other), |(o, _)| o, PhantomData) }

    /// Parse a pattern, but with an instance of another pattern on either end, yielding the output of the inner.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let ident = text::ident::<_, Simple<char>>()
    ///     .padded_by(just('!'));
    ///
    /// assert_eq!(ident.parse("!hello!"), Ok("hello".to_string()));
    /// assert!(ident.parse("hello!").is_err());
    /// assert!(ident.parse("!hello").is_err());
    /// assert!(ident.parse("hello").is_err());
    /// ```
    fn padded_by<U, P: Parser<I, U, Error = Self::Error> + Clone>(self, other: P) -> ThenIgnore<IgnoreThen<P, Self, U, O>, P, O, U>
        where Self: Sized
    { other.clone().ignore_then(self).then_ignore(other) }

    // fn then_catch(self, end: I) -> ThenCatch<Self, I> where Self: Sized { ThenCatch(self, end) }

    /// Parse the pattern surrounded by the given delimiters.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
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
    ///     .map(|s: String| s.parse().unwrap());
    ///
    /// let s_expr = recursive(|s_expr| s_expr
    ///     .padded()
    ///     .repeated()
    ///     .map(SExpr::List)
    ///     .delimited_by('(', ')')
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
    fn delimited_by(self, start: I, end: I) -> DelimitedBy<Self, I> where Self: Sized { DelimitedBy(self, start, end) }

    /// Parse one thing or, on failure, another thing.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let op = just::<_, Cheap<char>>('+')
    ///     .or(just('-'))
    ///     .or(just('*'))
    ///     .or(just('/'));
    ///
    /// assert_eq!(op.parse("+"), Ok('+'));
    /// assert_eq!(op.parse("/"), Ok('/'));
    /// assert!(op.parse("!").is_err());
    /// ```
    fn or<P: Parser<I, O>>(self, other: P) -> Or<Self, P> where Self: Sized { Or(self, other) }

    /// Apply a fallback recovery strategy to this parser should it fail.
    ///
    /// There is no silver bullet for error recovery, so this function allows you to specify one of several different
    /// strategies at the location of your choice.
    ///
    /// Note that for implementation reasons, adding an error recovery strategy can cause a parser to 'over-commit',
    /// missing potentially valid alternative parse routes (*TODO: document this and explain why and when it happens*).
    /// Rest assured that this case is generally quite rare and only happens for very loose, almost-ambiguous syntax.
    /// If you run into cases that you believe should parse but do not, try removing or moving recovery strategies to
    /// fix the problem.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Expr {
    ///     Error,
    ///     Int(String),
    ///     List(Vec<Expr>),
    /// }
    ///
    /// let expr = recursive::<_, _, _, _, Simple<char>>(|expr| expr
    ///     .separated_by(just(','))
    ///     .delimited_by('[', ']')
    ///     .map(Expr::List)
    ///     // If parsing a list expression fails, recover at the next delimiter, generating an error AST node
    ///     .recover_with(nested_delimiters('[', ']', [], || Expr::Error))
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
    fn recover_with<S: Strategy<I, O, Self::Error>>(self, strategy: S) -> Recovery<Self, S> where Self: Sized {
        Recovery(self, strategy)
    }

    /// Attempt to parse something, but only if it exists.
    ///
    /// If parsing of the pattern is successful, the output is `Some(_)`. Otherwise, the output is `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
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
    fn or_not(self) -> OrNot<Self> where Self: Sized { OrNot(self) }

    /// Parse an expression any number of times (including zero times).
    ///
    /// Input is eagerly parsed. Be aware that the parser will accept no occurences of the pattern too. Consider using
    /// [`Repeated::at_least`] instead if it better suits your use-case.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let num = filter::<_, _, Cheap<char>>(|c: &char| c.is_ascii_digit())
    ///     .repeated().at_least(1)
    ///     .collect::<String>()
    ///     .map(|s| s.parse().unwrap());
    ///
    /// let sum = num.then(just('+').ignore_then(num).repeated())
    ///     .foldl(|a, b| a + b);
    ///
    /// assert_eq!(sum.parse("2+13+4+0+5"), Ok(24));
    /// ```
    fn repeated(self) -> Repeated<Self> where Self: Sized { Repeated(self, 0, None) }

    /// Parse an expression, separated by another, any number of times.
    ///
    /// You can use [`SeparatedBy::allow_leading`] or [`SeparatedBy::allow_trailing`] to allow leading or trailing
    /// separators.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{prelude::*, error::Cheap};
    ///
    /// let shopping = text::ident::<_, Simple<char>>()
    ///     .padded()
    ///     .separated_by(just(','));
    ///
    /// assert_eq!(shopping.parse("eggs"), Ok(vec!["eggs".to_string()]));
    /// assert_eq!(shopping.parse("eggs, flour, milk"), Ok(vec!["eggs".to_string(), "flour".to_string(), "milk".to_string()]));
    /// ```
    ///
    /// See [`SeparatedBy::allow_leading`] and [`SeparatedBy::allow_trailing`] for more examples.
    fn separated_by<U, P: Parser<I, U>>(self, other: P) -> SeparatedBy<Self, P, U> where Self: Sized {
        SeparatedBy {
            a: self,
            b: other,
            at_least: 0,
            allow_leading: false,
            allow_trailing: false,
            phantom: PhantomData,
        }
    }

    /// Box the parser, yielding a parser that performs parsing through dynamic dispatch.
    ///
    /// Boxing a parser might be useful for:
    ///
    /// - Passing a parser over an FFI boundary
    ///
    /// - Getting around compiler implementation problems with long types such as
    ///   [this](https://github.com/rust-lang/rust/issues/54540).
    ///
    /// - Places where you need to name the type of a parser
    ///
    /// Boxing a parser is broadly equivalent to boxing other combinators, such as [`Iterator`].
    fn boxed<'a>(self) -> BoxedParser<'a, I, O, Self::Error> where Self: Sized + 'a {
        BoxedParser(Rc::new(self))
    }
}

impl<'a, I: Clone, O, T: Parser<I, O> + ?Sized> Parser<I, O> for &'a T {
    type Error = T::Error;

    fn parse_inner<D: Debugger>(&self, debugger: &mut D, stream: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> {
        debugger.invoke::<_, _, T>(*self, stream)
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> { #[allow(deprecated)] self.parse_inner(d, s) }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> { #[allow(deprecated)] self.parse_inner(d, s) }
}

impl<I: Clone, O, T: Parser<I, O> + ?Sized> Parser<I, O> for Box<T> {
    type Error = T::Error;

    fn parse_inner<D: Debugger>(&self, debugger: &mut D, stream: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> {
        debugger.invoke::<_, _, T>(&*self, stream)
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> { #[allow(deprecated)] self.parse_inner(d, s) }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> { #[allow(deprecated)] self.parse_inner(d, s) }
}

impl<I: Clone, O, T: Parser<I, O> + ?Sized> Parser<I, O> for Rc<T> {
    type Error = T::Error;

    fn parse_inner<D: Debugger>(&self, debugger: &mut D, stream: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> {
        debugger.invoke::<_, _, T>(&*self, stream)
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> { #[allow(deprecated)] self.parse_inner(d, s) }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> { #[allow(deprecated)] self.parse_inner(d, s) }
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
#[repr(transparent)]
pub struct BoxedParser<'a, I, O, E: Error<I>>(Rc<dyn Parser<I, O, Error = E> + 'a>);

impl<'a, I, O, E: Error<I>> Clone for BoxedParser<'a, I, O, E> {
    fn clone(&self) -> Self { Self(self.0.clone()) }
}

impl<'a, I: Clone, O, E: Error<I>> Parser<I, O> for BoxedParser<'a, I, O, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(&self, debugger: &mut D, stream: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> {
        #[allow(deprecated)]
        debugger.invoke(&self.0, stream)
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> { #[allow(deprecated)] self.parse_inner(d, s) }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> { #[allow(deprecated)] self.parse_inner(d, s) }
}
