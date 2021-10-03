# Chumsky

[![crates.io](https://img.shields.io/crates/v/chumsky.svg)](https://crates.io/crates/chumsky)
[![crates.io](https://docs.rs/chumsky/badge.svg)](https://docs.rs/chumsky)
[![License](https://img.shields.io/crates/l/chumsky.svg)](https://github.com/zesterer/chumsky)
[![actions-badge](https://github.com/zesterer/chumsky/workflows/Rust/badge.svg?branch=master)](https://github.com/zesterer/chumsky/actions)

A friendly parser combinator crate that makes writing [LL(k)](https://en.wikipedia.org/wiki/LL_parser) parsers with
error recovery and partial parsing easy.

## Features

- Lots of combinators!
- Generic across input, output, error, and span types
- Powerful error recovery strategies
- Inline mapping to your AST
- Text-specific parsers for both `u8`s and `char`s
- Recursive parsers
- Automatic support for backtracking, allowing the parsing of LL(k) grammars

## What *is* a parser combinator?

Parser combinators are a technique for implementing parsers by defining them in terms of other parsers. The resulting
parsers use a [recursive descent](https://en.wikipedia.org/wiki/Recursive_descent_parser) strategy for transforming an
input into an output. Using parser combinators to define parsers is roughly analagous to using Rust's
[`Iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html) trait to define iterative algorithms: the
type-driven API of `Iterator` makes it more difficult to make mistakes and easier to encode complicated iteration logic
than if one were to write the same code by hand. The same is true of parsers and parser combinators.

## Example [Brainfuck](https://en.wikipedia.org/wiki/Brainfuck) Parser

See [`examples/brainfuck.rs`](https://github.com/zesterer/chumsky/blob/master/examples/brainfuck.rs) for the full
interpreter (`cargo run --example brainfuck -- examples/sample.bf`).

```rust
use chumsky::prelude::*;

#[derive(Clone)]
enum Instr {
    Left, Right,
    Incr, Decr,
    Read, Write,
    Loop(Vec<Self>),
}

fn parser() -> impl Parser<char, Vec<Instr>, Error = Simple<char>> {
    recursive(|bf| bf.delimited_by('[', ']').map(Instr::Loop)
        .or(just('<').to(Instr::Left))
        .or(just('>').to(Instr::Right))
        .or(just('+').to(Instr::Incr))
        .or(just('-').to(Instr::Decr))
        .or(just(',').to(Instr::Read))
        .or(just('.').to(Instr::Write))
        .repeated())
}
```

Other examples include:

- A [JSON parser](https://github.com/zesterer/chumsky/blob/master/examples/json.rs) (`cargo run --example json --
  examples/sample.json`)
- An [interpreter for simple Rust-y language](https://github.com/zesterer/chumsky/blob/master/examples/nano_rust.rs)
  (`cargo run --example nano_rust -- examples/sample.nrs`)

## Error Recovery

Chumsky has support for error recovery, meaning that it can encounter a syntax error, report the error, and then
attempt to recover itself into a state in which it can continue parsing so that multiple errors can be produced at once
and a partial [AST](https://en.wikipedia.org/wiki/Abstract_syntax_tree) can still be generated from the input for future
compilation stages to consume.

However, there is no silver bullet strategy for error recovery. By definition, if the input to a parser is invalid then
the parser can only make educated guesses as to the meaning of the input. Different recovery strategies will work better
for different languages, and for different patterns within those languages.

Chumsky provides a variety of recovery strategies (each implementing the `Strategy` trait), but it's important to
understand that which you apply, where you apply them, and in what order will greatly affect the quality of the errors
that Chumsky is able to produce, along with the extent to which it is able to recover a useful AST. Where possible, you
should attempt more 'specific' recovery strategies first rather than those that mindlessly skip large swathes of the
input.

It is recommended that you experiment with applying different strategies in different situations and at different levels
of the parser to find a configuration that you are happy with. If none of the provided error recovery strategies cover
the specific pattern you wish to catch, you can even create your own by digging into Chumsky's internals and
implementing your own strategies! If you come up with a useful strategy, feel free to open a PR against the main repo!

## Planned Features

- Intrusive parsers (parsers that parse patterns within nested inputs, allowing you to move delimiter parsing to the
  lexing stage)
- A debugging mode (using `track_caller`) that allows backtrace-style debugging of parser behaviour to help you
  eliminate ambiguities, solve problems, and understand the route that the parser took through your grammar when
  processing inputs
- An optimised 'happy path' parser mode that skips error recovery & error generation
- An even faster 'validation' parser mode, guaranteed to not allocate, that doesn't generate outputs but just verifies
  the validity of an input

## Philosophy

Chumsky should:

- Be easy to use, even if the user doesn't understand the complexity that underpins parsing
- Be type-driven, pushing users away from anti-patterns at compile-time
- Be a mature, 'batteries-included' solution for context-free parsing by default. If you need to implement either
  `Parser` or `Strategy` by hand, that's a problem that needs fixing
- Be 'fast enough', but no faster (i.e: when there is a tradeoff between error quality and performance, Chumsky will
  always take the former option)
- Be modular and extensible, allowing users to implement their own parsers, recovery strategies, error types, spans, and
  be generic over both input tokens and the output AST

## Other Information

My apologies to Noam for choosing such an absurd name.

## License

Chumsky is licensed under the MIT license (see `LICENSE`) in the main repository.
