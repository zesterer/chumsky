# Key Concepts

This section is mostly a glossary of terms and concepts. Feel free to skip to the sections that most interest you.

- [What are parser combinators?](#what-are-parser-combinators)

    - [Parsers](#parsers)

    - [Declarative style](#declarative-style)

    - [Combinators](#combinators)

    - [Primitives](#primitives)

- [API features](#api-features)

    - [The `Parser` trait](#the-parser-trait)

    - [The `Input` trait](#the-input-trait)

    - [The `Error` trait](#the-error-trait)

    - [The `Span` trait](#the-span-trait)

# What are parser combinators?

Chumsky is a **declarative parser combinator** library. Let's break that down to explain what it means.

## Parsers

Parsers are programs (or, for our purposes, *functions*) which take **unstructured** inputs and produce
**structured** outputs according to a set of rules called a **grammar**.

What counts as structured and unstructured depends on the context. To a
[lexer](https://en.wikipedia.org/wiki/Lexical_analysis), a list of tokens might count as a structured output, but to the
parser that consumes them as an input, they look rather less structured.

Because the set of possible unstructured inputs to a parser (such as bytes in a text file) is generally larger than
those that can be correctly translated to the structured output according to the grammar rules (such as an
[Abstract Syntax Tree](https://en.m.wikipedia.org/wiki/Abstract_syntax_tree)), parsers need a way to generate **errors**
when these invalid inputs are encountered.

## Declarative style

If you've hand-written a parser before, it was likely in the
[**imperative**](https://en.wikipedia.org/wiki/Imperative_programming) style: which is to say that you used code to tell
your program *how* to parse inputs. This is a valid approach to writing parsers, and many successful parsers are written
in an imperative style.

However, imperative-style parsers are often extremely 'noisy': resulting in parser code that is long, difficult to
maintain, is hard to read, time-consuming to optimise, and easy to break, and difficult to debug.

In comparison, chumsky encourages you to write [**declarative**](https://en.wikipedia.org/wiki/Declarative_programming)
parsers. In the declarative style, instead of telling your code *how* to parse inputs, you tell it *what* to parse. This
is a much more grounded and to-the-point approach to implementing parsers, allowing you to focus on the grammar rules
you want to parse instead of spending ages debugging and maintaining imperative-style parser logic.

If you search for information about declarative parsers (and in particular, parser combinators), you'll often hear it
said that they're slow and imprecise. While this might have been true in decades gone by, modern optimising compilers -
and in particular Rust's powerful type system - make the development of expressive declarative parsers that are as fast (or
faster!) than hand-written parsers both easy and quick.

## Combinators

Modern software is written primarily through through the use of *functions*. Each function performs a specific task and
may call out to sub-functions. To create a whole program, it is necessary to **combine** functions to get the desired
behaviour of the program as a whole.

Parser combinators take this approach and apply it to parsing: a parser written with a combinator approach is composed
of many smaller sub-parsers that are each able to process a sub-section of the overall grammar rules. These sub-parsers
are then *combined* with parser operators known as **combinators** that define how they relate to one-another.

Chumsky comes with many [`combinator`]s that allow the creation of even very complex grammars. Indeed, parsers for
entire programming languages may be easily written with chumsky.

As with most things, it's turtles all the way down: each sub-parser is then composed of sub-sub-parsers, which is itself
composed of sub-sub-sub-parsers, until we reach the most basic elements of the parser logic.

🐢

## Primitives

Primitives are the most basic elements of chumsky's parser logic. They are built-in components provided by chumsky
(although it is possible to write your own!). Primitives each perform a very simple action that by itself seems almost
trivial. For example, they might recognise a specific keyword or even just a single character.

Chumsky comes with several [`primitive`] parsers that each perform a specific job.

# API features

## The [`Parser`] trait

A fundamental concept in chumsky is that of the [`Parser`] trait. All parser (both combinators and primitives) implement
it and the combinator methods on it are the primary way through which a parser is defined.

[`Parser`] also provides several *invocation* methods such as [`Parser::parse`] and [`Parser::check`]: these functions
allow you to actually give inputs to your parser and have it generate outputs and/or errors.

Check out the [`primitive`], [`combinator`], [`mod@recursive`], and [`mod@regex`] modules for examples of some of the parsers
that chumsky provides.

## The [`Input`] trait

The [`Input`] trait is implemented by all types that can act as inputs to chumsky parsers. For example, it is
implemented by types such as:

- `&[T]`: Array slices

- `&str`: String slices

- [`Stream<I>`]: Dynamically-growing token streams

Certain inputs have special properties. For example, it is possible to borrow `&T` tokens from `&[T]` array slices, but
not `char`s from `&str` string slices (due to their UTF-8 encoding). Additionally, some inputs can have sub-slices taken
from them. All of these operations are potentially useful to a parser, so chumsky expresses them with a set of extension
traits that add extra functionality on top of the base [`Input`] trait:

- [`ValueInput`]: for inputs that can have tokens copied/cloned from them by-value

- [`BorrowInput`]: for inputs that can have individual tokens borrowed from them

- [`SliceInput`]: for inputs that can have entire sub-slices of tokens borrowed from them

- [`StrInput`]: for inputs that 'look like' text strings: ASCII byte slices (`&[u8]`) and UTF-8 string slices (`&str`)

Taken together, these traits give chumsky the power to use many different types as input: bytes, strings, tokens,
token trees, iterators, and much more besides.

## The [`Error`] trait

As discussed previously, parsers commonly need to be able to handle inputs that don't conform to the grammar rules that
they implement. To do this, they need to be able to emit errors that can then be processed by either the system that
invoked the parser, or by a human user, in order to communicate what went wrong.

Chumsky provides support for expressive error generation through its [`Error`] trait, along with a series of built-in
error types that have different tradeoffs:

- [`EmptyErr`]: the default 'null' error that doesn't record any useful information other than the fact that an error
  occurred

- [`Cheap`]: a very efficient error type that records only the span of the input that triggered the error

- [`Simple`]: a simplistic error type that records both the span that triggered the error and whatever token was
  erroneously found

- [`Rich`]: a very information-rich error type that records:

    - The span that triggered the error

    - The token that was erroneously found instead

    - A list of tokens or patterns that were expected at the span location instead

[`Rich`] also supports many additional features such as custom error messages, labelling (see [`Parser::labelled`]) and
error merging.

Obviously, errors that express more detailed information are also slower to generate and hence reduce the performance of
the overall parser. In benchmarks, we tend to find that parsers using [`Rich`] typically run at about half the speed as
those using [`EmptyErr`], although this is very likely to improve as time goes on.

It is typical to take the data encoded in these types and give them to a 'diagnostic generator', a tool intended to turn
error information into pretty human-readable displays suited for printing into a terminal, displaying in an IDE, or
whatever other form of output is required.

## The [`Span`] trait

Spans are ranges (usually byte offsets, but you can use whatever is most convenient for you) in the original source code
that can be used to reference sections of the code in error or warning messages.

Chumsky has full support for spans and also allows you to define your own custom spans with ease by simply implementing
the [`Span`] trait. Additionally, chumsky comes with a built-in span type, [`SimpleSpan`], and a variety of
implementations for types in Rust's standard library such as [`std::ops::Range<usize>`].

Chumsky will use its internal knowledge of your parser to generate spans for you whenever you need them, such as for
attaching to nodes of an abstract syntax tree. See [`Parser::map_with`] for more information.
