# Chumsky

[![crates.io](https://img.shields.io/crates/v/chumsky.svg)](https://crates.io/crates/chumsky)
[![crates.io](https://docs.rs/chumsky/badge.svg)](https://docs.rs/chumsky)
[![License](https://img.shields.io/crates/l/chumsky.svg)](https://github.com/zesterer/chumsky)
[![actions-badge](https://github.com/zesterer/chumsky/workflows/Rust/badge.svg?branch=master)](https://github.com/zesterer/chumsky/actions)

A friendly parser combinator crate that makes writing [LL(k)](https://en.wikipedia.org/wiki/LL_parser) parsers with
error recovery and partial parsing easy.

<a href = "https://www.github.com/zesterer/tao">
    <img src="https://raw.githubusercontent.com/zesterer/chumsky/master/misc/example.png" alt="Example usage with my own language, Tao"/>
</a>

*Note: Error diagnostic rendering is performed by [Ariadne](https://github.com/zesterer/ariadne)*

## Features

- Lots of combinators!
- Generic across input, output, error, and span types
- Powerful error recovery strategies
- Inline mapping to your AST
- Text-specific parsers for both `u8`s and `char`s
- Recursive parsers
- Automatic support for backtracking, allowing parsing of LL(k) grammars
- Parsing of nesting inputs, allowing you to move delimiter parsing to the lexical stage (as Rust does!)

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

## *What* is a parser combinator?

Parser combinators are a technique for implementing parsers by defining them in terms of other parsers. The resulting
parsers use a [recursive descent](https://en.wikipedia.org/wiki/Recursive_descent_parser) strategy to transform a stream
of tokens into an output. Using parser combinators to define parsers is roughly analagous to using Rust's
[`Iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html) trait to define iterative algorithms: the
type-driven API of `Iterator` makes it more difficult to make mistakes and easier to encode complicated iteration logic
than if one were to write the same code by hand. The same is true of parser combinators.

## *Why* use parser combinators?

Writing parsers with good error recovery is conceptually difficult and time-consuming. It requires understanding the
intricacies of the recursive descent algorithm, and then implementing recovery strategies on top of it. If you're
developing a programming language, you'll almost certainly change your mind about syntax in the process, leading to some
slow and painful parser refactoring. Parser combinators solve both problems by providing an ergonomic API that allows
for rapidly iterating upon a syntax.

Parser combinators are also a great fit for domain-specific languages for which an existing parser does not exist.
Writing a reliable, fault-tolerant parser for such situations can go from being a multi-day task to a half-hour task
with the help of a decent parser combinator library.

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
implementing your own strategies! If you come up with a useful strategy, feel free to open a PR against the
[main repository](https://github.com/zesterer/chumsky/)!

## Performance

Chumsky focuses on high-quality errors and ergonomics over performance. That said, it's important that Chumsky can keep
up with the rest of your compiler! Unfortunately, it's *extremely* difficult to come up with sensible benchmarks given
that exactly how Chumsky performs depends entirely on what you are parsing, how you structure your parser, which
patterns the parser attempts to match first, how complex your error type is, what is involved in constructing your AST,
etc. All that said, here are some numbers from the
[JSON benchmark](https://github.com/zesterer/chumsky/blob/master/benches/json.rs) included in the repository running on
my Ryzen 7 3700x.

```ignore
test chumsky ... bench:   5,969,794 ns/iter (+/- 75,548)
test pom     ... bench:  12,858,594 ns/iter (+/- 181,703)
```

I've included results from [`pom`](https://github.com/J-F-Liu/pom), another parser combinator crate with a similar
design, as a point of reference. The sample file being parsed is broadly represenative of typical JSON data and has
3,018 lines. This translates to a little over 500,000 lines of JSON per second.

Clearly, this is somewhat slower than a well-optimised hand-written parser: but that's okay! Chumsky's goal is to be
*fast enough*. If you've written enough code in your language that parsing performance even starts to be a problem,
you've already committed enough time and resources to your language that hand-writing a parser is the best choice going!

## Planned Features

- An optimised 'happy path' parser mode that skips error recovery & error generation
- An even faster 'validation' parser mode, guaranteed to not allocate, that doesn't generate outputs but just verifies
  the validity of an input

## Philosophy

Chumsky should:

- Be easy to use, even if you doesn't understand exactly what the parser is doing under the hood
- Be type-driven, pushing users away from anti-patterns at compile-time
- Be a mature, 'batteries-included' solution for context-free parsing by default. If you need to implement either
  `Parser` or `Strategy` by hand, that's a problem that needs fixing
- Be 'fast enough', but no faster (i.e: when there is a tradeoff between error quality and performance, Chumsky will
  always take the former option)
- Be modular and extensible, allowing users to implement their own parsers, recovery strategies, error types, spans, and
  be generic over both input tokens and the output AST

## Notes

My apologies to Noam for choosing such an absurd name.

## License

Chumsky is licensed under the MIT license (see `LICENSE` in the main repository).
