# Chumsky

[![crates.io](https://img.shields.io/crates/v/chumsky.svg)](https://crates.io/crates/chumsky)
[![crates.io](https://docs.rs/chumsky/badge.svg)](https://docs.rs/chumsky)
[![License](https://img.shields.io/crates/l/chumsky.svg)](https://github.com/zesterer/chumsky)
[![actions-badge](https://github.com/zesterer/chumsky/workflows/Rust/badge.svg?branch=master)](https://github.com/zesterer/chumsky/actions)

A friendly parser combinator crate that makes writing LL(k) parsers with powerful error recovery easy.

## Example

Here follows a [Brainfuck](https://en.wikipedia.org/wiki/Brainfuck) parser. See `examples/` for the full interpreter.

```rs
fn parser() -> impl Parser<char, Vec<Instr>, Error = Simple<char>> {
    use Instr::*;
    recursive(|bf| bf.delimited_by('[', ']').map(Loop)
        .or(just('<').to(Left))
        .or(just('>').to(Right))
        .or(just('+').to(Incr))
        .or(just('-').to(Decr))
        .or(just(',').to(Read))
        .or(just('.').to(Write))
        .repeated())
}
```

Other examples in this repository include a **JSON parser**, a **Brainfuck interpreter**, and an interpreter for a
simple dynamically-typed **Rust-like programming language**.

## Features

- Generic combinator parsing
- Error recovery
- Recursive parsers
- Text-specific parsers & utilities
- Custom error types

## Planned Features

- Nested parsers (parsers that parse patterns within nested tokens)
- A debugging mode (using `track_caller`) that allows inspecting the behaviour of parsers
- Optimised 'fast path' pass that skips error generation

## Other Information

My apologies to Noam for choosing such an absurd name.

## License

Chumsky is licensed under the MIT license (see `LICENSE`) in the main repository.
