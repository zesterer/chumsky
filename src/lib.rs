//! A friendly parser combinator crate that makes writing LL(1) parsers with error recovery easy.
//!
//! ## Example
//!
//! Here follows a [Brainfuck](https://en.wikipedia.org/wiki/Brainfuck) parser. See `examples/` for the full interpreter.
//!
//! ```
//! use chumsky::prelude::*;
//!
//! #[derive(Clone)]
//! enum Instr {
//!     Invalid,
//!     Left, Right,
//!     Incr, Decr,
//!     Read, Write,
//!     Loop(Vec<Self>)
//! }
//!
//! fn parser() -> impl Parser<char, Vec<Instr>, Error = Simple<char>> {
//!     use Instr::*;
//!     recursive(|bf| bf.delimited_by('[', ']').map(|xs| xs.map_or(Invalid, Loop))
//!         .or(just('<').to(Left))
//!         .or(just('>').to(Right))
//!         .or(just('+').to(Incr))
//!         .or(just('-').to(Decr))
//!         .or(just(',').to(Read))
//!         .or(just('.').to(Write))
//!         .repeated())
//! }
//! ```
//!
//! ## Features
//!
//! - Generic combinator parsing
//! - Error recovery
//! - Recursive parsers
//! - Text-specific parsers & utilities
//! - Custom error types
//!
//! ## What is LL(k) parsing?
//!
//! We can think of parsing like navigating a maze that has no cycles. As we walk towards what we hope is the exit we
//! will, from time to time, come across splits in the path. Our job is to decide which path to take in order to reach
//! the exit. How do we do this?
//!
//! Thankfully, we have signposts at every turning in the form of upcoming tokens to parse. Unfortunately, these
//! signposts don't tell us exactly where to go: they just give us an idea of what obstacles might be lying ahead. We
//! also have a way to see into the future using 'token lookahead'. Lookahead means that at every split in the path, we
//! get a chance to peer into the distance to see what lies ahead on each possible path before deciding to commit to
//! it. The distance that we're allowed to look is the 'k' in LL(k) parsing. Parsers capable of taking a walk into the
//! future, realising they've taken a wrong turn, and retracing their steps are known as 'backtracking' parsers for
//! this reason.
//!
//! ## LL(1) parsing: limitations and advantages
//!
//! Chumsky is designed for LL(1) parsing. This means that at each split in the path, we only get to see the very next
//! token in advance before making a choice about which path to proceed down. In effect, we need to be able to figure
//! out how to proceed using only the very next token in the input sequence. No backtracking allowed!
//!
//! This may initially seem like a serious limitation and it is, at least in theory. In practice, we can eliminate many
//! of these limitations by deploying *parsing passes*. A common example of multi-pass parsing is the way in which
//! compilers for C-like languages generally perform an initial lexing (also called 'tokenization') pass to split
//! the source code into logical groups of characters known as 'tokens' and later feed these tokens into a secondary
//! pass to generate the program's abstract syntax tree. This isn't just a workaround for the limitations of an LL(1)
//! parser either: splitting parsing into multiple passes makes writing and validating each pass simpler and allows for
//! tools like syntax highlighters that make use of earlier passes only to be built on top of the same codebase.
//!
//! All of this considered, LL(1) parsers are powerful tools that continue to be a relevant and effective route for
//! parsing even (and, perhaps, *in particular*) the latest generations of programming languages.
//!
//! Why use LL(1) parsing when more powerful backtracking alternatives exist? The answer, in my view, comes down to
//! three main points.
//!
//! - **Simplicity**: LL(1) grammars are usually easier to write (and, arguably, read) than more complex grammars.
//!
//! - **Performance**: LL(1) parsing does not require backtracking (because backtracking is impossible). This means
//!   that parsing can only ever proceed in the forward direction, meaning that parsing has *linear* (i.e: **O(n)**)
//!   time complexity. Compare this to other parsing techniques, for which exponential time is virtually the norm.
//!
//! - **Error recovery**: Because parsers of LL(1) grammars do not perform backtracking, there are fewer potential
//!   parse paths to consider: this makes it more likely that errors can be recovered from without misinterpreting
//!   syntax and makes it more likely that errors relate to the syntax that the user is attempting to write.

#![deny(missing_docs)]
// TODO: Enable when stable
//#![feature(once_cell)]

/// Traits that allow chaining parser outputs together.
pub mod chain;
/// Combinators that allow combining and extending existing parsers.
pub mod combinator;
/// Error types, traits and utilities.
pub mod error;
/// Parser primitives that accept specific token patterns.
pub mod primitive;
/// Recursive parsers (parser that include themselves within their patterns).
pub mod recursive;
/// Token streams and behaviours.
pub mod stream;
/// Text-specific parsers and utilities.
pub mod text;

pub use crate::error::{Error, Span};

use crate::{chain::Chain, combinator::*, primitive::*, stream::*};

use std::{
    iter::Peekable,
    marker::PhantomData,
    rc::Rc,
    // TODO: Enable when stable
    //lazy::OnceCell,
};

/// Commonly used functions, traits and types.
pub mod prelude {
    pub use super::{
        error::{Error as _, Simple},
        primitive::{any, end, filter, filter_map, just, none_of, one_of, seq},
        recursive::recursive,
        text,
        text::{whitespace, TextParser as _},
        BoxedParser, Parser,
    };
}

fn or_zip_with<T, F: FnOnce(T, T) -> T>(a: Option<T>, b: Option<T>, f: F) -> Option<T> {
    match (a, b) {
        (Some(a), Some(b)) => Some(f(a, b)),
        (a, b) => a.or(b),
    }
}

fn zip_or<T, F: FnOnce(T, T) -> T>(a: Option<T>, b: T, f: F) -> T {
    match a {
        Some(a) => f(a, b),
        None => b,
    }
}

type ParserFn<'a, I, O, E> = dyn Fn(&mut dyn Stream<I, <E as Error<I>>::Span>, &mut Vec<E>) -> (usize, Result<(O, Option<E>), E>)
    + 'a;

/// A trait implemented by parsers.
///
/// Parsers take a stream of tokens of type `I` and attempt to parse them into a value of type `O`. In doing so, they
/// may encounter errors. These need not be fatal to the parsing process: syntactic errors can be recovered from and a
/// valid output may still be generated alongside any syntax errors that were encountered along the way. Usually, this
/// output comes in the form of an [Abstract Syntax Tree](https://en.wikipedia.org/wiki/Abstract_syntax_tree) (AST).
///
/// Parsers currently only support LL(1) grammars. More concretely, this means that the rules that compose this parser
/// are only permitted to 'look' a single token into the future to determine the path through the grammar rules to be
/// taken by the parser. Unlike other techniques, such as recursive decent, arbitrary backtracking is not permitted.
/// The reasons for this are numerous, but perhaps the most obvious is that it makes error detection and recovery
/// significantly simpler and easier. In the future, this crate may be extended to support more complex grammars.
///
/// LL(1) parsers by themselves are not particularly powerful. Indeed, even very old languages such as C cannot parsed
/// by an LL(1) parser in a single pass. However, this limitation quickly vanishes (and, indeed, makes the design of
/// both the language and the parser easier) when one introduces multiple passes. For example, C compilers generally
/// have a lexical pass prior to the main parser that groups the input characters into tokens.
pub trait Parser<I, O> {
    /// The type of errors emitted by this parser.
    type Error: Error<I>; // TODO when default associated types are stable: = Simple<I>;

    /// Parse a stream with all the bells & whistles. You can use this to implement your own parser combinators. Note
    /// that both the signature and semantic requirements of this function are very likely to change in later versions.
    /// Where possible, prefer more ergonomic combinators provided elsewhere in the crate rather than implementing your
    /// own.
    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(
        &self,
        stream: &mut S,
        errors: &mut Vec<Self::Error>,
    ) -> (usize, Result<(O, Option<Self::Error>), Self::Error>)
    where
        Self: Sized;

    /// Parse an iterator of tokens, yielding an output if possible, and any errors encountered along the way.
    ///
    /// If you don't care about producing an output if errors are encountered, use `Parser::parse` instead.
    fn parse_recovery<S: IntoStream<I, <Self::Error as Error<I>>::Span>>(
        &self,
        stream: S,
    ) -> (Option<O>, Vec<Self::Error>)
    where
        Self: Sized,
    {
        let mut errors = Vec::new();
        match self.parse_inner(&mut stream.into_stream(), &mut errors).1 {
            Ok((o, _)) => (Some(o), errors),
            Err(e) => {
                errors.push(e);
                (None, errors)
            }
        }
    }

    /// Parse an iterator of tokens, yielding an output *or* any errors that were encountered along the way.
    ///
    /// If you wish to attempt to produce an output even if errors are encountered, use `Parser::parse_recovery`.
    fn parse<S: IntoStream<I, <Self::Error as Error<I>>::Span>>(
        &self,
        stream: S,
    ) -> Result<O, Vec<Self::Error>>
    where
        Self: Sized,
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

    /// Map the output of this parser to aanother value.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Token { Word(String), Num(u64) }
    ///
    /// let word = filter::<_, _, Simple<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated_at_least(1)
    ///     .collect::<String>()
    ///     .map(Token::Word);
    ///
    /// let num = filter::<_, _, Simple<char>>(|c: &char| c.is_ascii_digit())
    ///     .repeated_at_least(1)
    ///     .collect::<String>()
    ///     .map(|s| Token::Num(s.parse().unwrap()));
    ///
    /// let token = word.or(num);
    ///
    /// assert_eq!(token.parse("test"), Ok(Token::Word("test".to_string())));
    /// assert_eq!(token.parse("42"), Ok(Token::Num(42)));
    /// ```
    fn map<U, F: Fn(O) -> U>(self, f: F) -> Map<Self, F, O>
    where
        Self: Sized,
    {
        Map(self, f, PhantomData)
    }

    /// Map the output of this parser to another value, making use of the pattern's span.
    fn map_with_span<U, F: Fn(O, Option<<Self::Error as Error<I>>::Span>) -> U>(
        self,
        f: F,
    ) -> MapWithSpan<Self, F, O>
    where
        Self: Sized,
    {
        MapWithSpan(self, f, PhantomData)
    }

    /// Map the primary error of this parser to another value.
    ///
    /// This does not map error emitted by sub-patterns within the parser.
    fn map_err<F: Fn(Self::Error) -> Self::Error>(self, f: F) -> MapErr<Self, F>
    where
        Self: Sized,
    {
        MapErr(self, f)
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
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let digits = text::digits()
    ///     .collect::<String>()
    ///     .padded_by(end())
    ///     .labelled("number");
    ///
    /// assert_eq!(digits.parse("42"), Ok("42".to_string()));
    /// assert_eq!(digits.parse("hello"), Err(vec![Simple::expected_label_found(Some(0..1), "number", Some('h'))]));
    /// ```
    fn labelled<L: Into<<Self::Error as Error<I>>::Pattern> + Clone>(
        self,
        label: L,
    ) -> Label<Self, L>
    where
        Self: Sized,
    {
        Label(self, label)
    }

    /// Transform all outputs of this parser to a pretermined value.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// enum Op { Add, Sub, Mul, Div }
    ///
    /// let op = just::<_, Simple<char>>('+').to(Op::Add)
    ///     .or(just('-').to(Op::Sub))
    ///     .or(just('*').to(Op::Mul))
    ///     .or(just('/').to(Op::Div));
    ///
    /// assert_eq!(op.parse("+"), Ok(Op::Add));
    /// assert_eq!(op.parse("/"), Ok(Op::Div));
    /// ```
    fn to<U: Clone>(self, x: U) -> To<Self, O, U>
    where
        Self: Sized,
    {
        To(self, x, PhantomData)
    }

    /// Left-fold the output of the parser into a single value, where the output is of type `(_, Vec<_>)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let int = text::int::<Simple<char>>()
    ///     .collect::<String>()
    ///     .map(|s| s.parse().unwrap());
    ///
    /// let sum = int
    ///     .then(just('+').padding_for(int).repeated())
    ///     .foldl(|a, b| a + b);
    ///
    /// assert_eq!(sum.parse("1+12+3+9"), Ok(25));
    /// assert_eq!(sum.parse("6"), Ok(6));
    /// ```
    fn foldl<A, B, F: Fn(A, B) -> A>(self, f: F) -> Foldl<Self, F, A, B>
    where
        Self: Parser<I, (A, Vec<B>)> + Sized,
    {
        Foldl(self, f, PhantomData)
    }

    /// Right-fold the output of the parser into a single value, where the output is of type `(Vec<_>, _)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let int = text::int::<Simple<char>>()
    ///     .collect::<String>()
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
    fn foldr<'a, A, B, F: Fn(A, B) -> B + 'a>(self, f: F) -> Foldr<Self, F, A, B>
    where
        Self: Parser<I, (Vec<A>, B)> + Sized,
    {
        Foldr(self, f, PhantomData)
    }

    /// Ignore the output of this parser, yielding `()` as an output instead.
    ///
    /// This can be used to reduce the cost of passing by avoiding unnecessary allocations (most collections containing
    /// [ZSTs](https://doc.rust-lang.org/nomicon/exotic-sizes.html#zero-sized-types-zsts) do
    /// [not allocate](https://doc.rust-lang.org/std/vec/struct.Vec.html#guarantees)). For example, it's common to want
    /// to ignore whitespace in many grammars.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// // A parser that parses any number of whitespace characters without allocating
    /// let whitespace = filter::<_, _, Simple<char>>(|c: &char| c.is_whitespace())
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

    /// Collect the output of this parser into a collection.
    ///
    /// This is commonly useful for collecting [`Vec<char>`] outputs into [`String`]s.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let word = filter::<_, _, Simple<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated()
    ///     .collect::<String>();
    ///
    /// assert_eq!(word.parse("hello"), Ok("hello".to_string()));
    /// ```
    fn collect<C: core::iter::FromIterator<O::Item>>(self) -> Map<Self, fn(O) -> C, O>
    where
        Self: Sized,
        O: IntoIterator,
    {
        self.map(|items| items.into_iter().collect())
    }

    /// Parse one thing and then another thing, yielding a tuple of the two outputs.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let word = filter::<_, _, Simple<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated_at_least(1)
    ///     .collect::<String>();
    /// let two_words = word.padded_by(just(' ')).then(word);
    ///
    /// assert_eq!(two_words.parse("dog cat"), Ok(("dog".to_string(), "cat".to_string())));
    /// assert!(two_words.parse("hedgehog").is_err());
    /// ```
    fn then<U, P: Parser<I, U>>(self, other: P) -> Then<Self, P>
    where
        Self: Sized,
    {
        Then(self, other)
    }

    /// Parse one thing and then another thing, attempting to chain the two outputs into a [`Vec`].
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let int = just('-').or_not()
    ///     .chain(filter::<_, _, Simple<char>>(|c: &char| c.is_ascii_digit() && *c != '0')
    ///         .chain(filter::<_, _, Simple<char>>(|c: &char| c.is_ascii_digit()).repeated()))
    ///     .or(just('0').map(|c| vec![c]))
    ///     .padded_by(end())
    ///     .collect::<String>()
    ///     .map(|s| s.parse().unwrap());
    ///
    /// assert_eq!(int.parse("0"), Ok(0));
    /// assert_eq!(int.parse("415"), Ok(415));
    /// assert_eq!(int.parse("-50"), Ok(-50));
    /// assert!(int.parse("-0").is_err());
    /// assert!(int.parse("05").is_err());
    /// ```
    fn chain<T, U, P: Parser<I, U, Error = Self::Error>>(
        self,
        other: P,
    ) -> Map<Then<Self, P>, fn((O, U)) -> Vec<T>, (O, U)>
    where
        Self: Sized,
        U: Chain<T>,
        O: Chain<T>,
    {
        self.then(other).map(|(a, b)| {
            let mut v = Vec::with_capacity(a.len() + b.len());
            a.append(&mut v);
            b.append(&mut v);
            v
        })
    }

    /// Flatten a nested collection.
    fn flatten<T, Inner>(self) -> Map<Self, fn(O) -> Vec<T>, O>
    where
        Self: Sized,
        O: IntoIterator<Item = Inner>,
        Inner: IntoIterator<Item = T>,
    {
        self.map(|xs| xs.into_iter().flat_map(IntoIterator::into_iter).collect())
    }

    /// Parse one thing and then another thing, yielding only the output of the latter.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let zeroes = filter::<_, _, Simple<char>>(|c: &char| *c == '0').ignored().repeated();
    /// let digits = filter(|c: &char| c.is_ascii_digit()).repeated();
    /// let integer = zeroes
    ///     .padding_for(digits)
    ///     .collect::<String>()
    ///     .map(|s| s.parse().unwrap());
    ///
    /// assert_eq!(integer.parse("00064"), Ok(64));
    /// assert_eq!(integer.parse("32"), Ok(32));
    /// ```
    fn padding_for<U, P: Parser<I, U>>(self, other: P) -> PaddingFor<Self, P, O, U>
    where
        Self: Sized,
    {
        Map(Then(self, other), |(_, u)| u, PhantomData)
    }

    /// Parse one thing and then another thing, yielding only the output of the former.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let word = filter::<_, _, Simple<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated_at_least(1)
    ///     .collect::<String>();
    ///
    /// let punctuated = word
    ///     .padded_by(just('!').or(just('?')).or_not());
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
    fn padded_by<U, P: Parser<I, U>>(self, other: P) -> PaddedBy<Self, P, O, U>
    where
        Self: Sized,
    {
        Map(Then(self, other), |(o, _)| o, PhantomData)
    }

    // fn then_catch(self, end: I) -> ThenCatch<Self, I> where Self: Sized { ThenCatch(self, end) }

    /// Parse the pattern surrounded by the given delimiters, performing error recovery where possible.
    ///
    /// If parsing of the inner pattern is successful, the output is `Some(_)`. If an error occurs, the output is
    /// `None`.
    ///
    /// The delimiters are assumed to allow nesting, so error recovery will attempt to balance the delimiters where
    /// possible. A syntax error within the delimiters should not prevent correct parsing of tokens beyond the
    /// delimiters.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// // A LISP-style S-expression
    /// #[derive(Debug, PartialEq)]
    /// enum SExpr {
    ///     Error,
    ///     Ident(String),
    ///     Num(u64),
    ///     List(Vec<SExpr>),
    /// }
    ///
    /// let ident = filter::<_, _, Simple<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated_at_least(1)
    ///     .collect::<String>();
    ///
    /// let num = text::int()
    ///     .collect::<String>()
    ///     .map(|s| s.parse().unwrap());
    ///
    /// let s_expr = recursive(|s_expr| s_expr
    ///     .padded()
    ///     .repeated()
    ///     .delimited_by('(', ')')
    ///     .map(|list| list.map_or(SExpr::Error, SExpr::List))
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
    ///
    /// // An input with a syntax error at position 11! Thankfully, we're able to recover
    /// // and still produce a useful output for later compilation stages (i.e: type-checking).
    /// assert_eq!(
    ///     s_expr.parse_recovery("(add (mul ! 3) 15)"),
    ///     (
    ///         Some(SExpr::List(vec![
    ///             SExpr::Ident("add".to_string()),
    ///             SExpr::Error,
    ///             SExpr::Num(15),
    ///         ])),
    ///         vec![Simple::expected_token_found(Some(10..11), vec!['(', '0', ')'], Some('!'))], // A syntax error!
    ///     ),
    /// );
    /// ```
    fn delimited_by(self, start: I, end: I) -> DelimitedBy<Self, I>
    where
        Self: Sized,
    {
        DelimitedBy(self, start, end)
    }

    /// Parse one thing or, on failure, another thing.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let op = just::<_, Simple<char>>('+')
    ///     .or(just('-'))
    ///     .or(just('*'))
    ///     .or(just('/'));
    ///
    /// assert_eq!(op.parse("+"), Ok('+'));
    /// assert_eq!(op.parse("/"), Ok('/'));
    /// assert!(op.parse("!").is_err());
    /// ```
    fn or<P: Parser<I, O>>(self, other: P) -> Or<Self, P>
    where
        Self: Sized,
    {
        Or(self, other)
    }

    /// Attempt to parse something, but only if it exists.
    ///
    /// If parsing of the pattern is successful, the output is `Some(_)`. Otherwise, the output is `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let word = filter::<_, _, Simple<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated_at_least(1)
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

    /// Parse an expression any number of times (including zero times).
    ///
    /// Input is eagerly parsed. Be aware that the parser will accept no occurences of the pattern too. Consider using
    /// [`Parser::repeated_at_least`] instead if it better suits your use-case.
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let num = filter::<_, _, Simple<char>>(|c: &char| c.is_ascii_digit())
    ///     .repeated_at_least(1)
    ///     .collect::<String>()
    ///     .map(|s| s.parse().unwrap());
    ///
    /// let sum = num.then(just('+').padding_for(num).repeated())
    ///     .foldl(|a, b| a + b);
    ///
    /// assert_eq!(sum.parse("2+13+4+0+5"), Ok(24));
    /// ```
    fn repeated(self) -> Repeated<Self>
    where
        Self: Sized,
    {
        Repeated(self, 0)
    }

    /// Parse an expression at least a given number of times.
    ///
    /// Input is eagerly parsed. If `n` is 0, this function is equivalent to [`Parser::repeated`]
    ///
    /// # Examples
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// let long_word = filter::<_, _, Simple<char>>(|c: &char| c.is_alphabetic())
    ///     .repeated_at_least(5)
    ///     .collect::<String>();
    ///
    /// assert_eq!(long_word.parse("hello"), Ok("hello".to_string()));
    /// assert!(long_word.parse("hi").is_err());
    /// ```
    fn repeated_at_least(self, n: usize) -> Repeated<Self>
    where
        Self: Sized,
    {
        Repeated(self, n)
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
    /// Boxing a parser is loosely equivalent to boxing other combinators, such as [`Iterator`].
    fn boxed<'a>(self) -> BoxedParser<'a, I, O, Self::Error>
    where
        Self: Sized + 'a,
    {
        BoxedParser(Rc::new(
            move |mut stream: &mut dyn Stream<I, <Self::Error as Error<I>>::Span>, errors| {
                self.parse_inner(&mut stream, errors)
            },
        ))
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
#[repr(transparent)]
pub struct BoxedParser<'a, I, O, E: Error<I>>(Rc<ParserFn<'a, I, O, E>>);

impl<'a, I, O, E: Error<I>> Clone for BoxedParser<'a, I, O, E> {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

impl<'a, I, O, E: Error<I>> Parser<I, O> for BoxedParser<'a, I, O, E> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(
        &self,
        stream: &mut S,
        errors: &mut Vec<Self::Error>,
    ) -> (usize, Result<(O, Option<E>), E>) {
        (self.0)(stream, errors)
    }
}
