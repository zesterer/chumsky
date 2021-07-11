# Chumsky

A friendly parser combinator crate that makes writing LL-1 parsers with error recovery easy.

## Example

Here follows a [Brainfuck](https://en.wikipedia.org/wiki/Brainfuck) parser. See `examples/` for the full interpreter.

```rs
fn parser() -> impl Parser<char, Vec<Instr>> {
    use Instr::*;
    recursive(|bf| bf.delimited_by('[', ']').map(|xs| xs.map_or(Invalid, Loop))
        .or(just('<').to(Left))
        .or(just('>').to(Right))
        .or(just('+').to(Incr))
        .or(just('-').to(Decr))
        .or(just(',').to(Read))
        .or(just('.').to(Write))
        .repeated())
}
```

## Features

- Generic combinator parsing
- Error recovery
- Recursive parsers
- Text-specific parsers & utilities
- Custom error types

## Planned Features

- Nested parsers

## Other Information

My apologies to Noam for choosing such an absurd name.

## License

Lagoon is licensed under the MIT license (see `LICENSE`) in the main repository.
