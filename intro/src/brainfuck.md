# A Simple Example

*Please note that this breakdown is kept up to date with the `master` branch and not the most stable release: small
details may differ!*

Before getting our hands dirty with Chumsky, we are going to take a quick look at
what a parser for the [Brainfuck]() language looks like. 

## The Language
<hr>

The language is an esoteric programming language with all of 8 commands. The fit nicely in a table,
so here they are:

Char | Meaning
---|---
`>`| Increment the data pointer by one (to point to the next cell to the right). 
`<`| Decrement the data pointer by one (to point to the next cell to the left).
`+`| Increment the byte at the data pointer by one.
`-`| Decrement the byte at the data pointer by one. 
`.`| Output the byte at the data pointer.
`,`| Accept one byte of input, storing its value in the byte at the data pointer. 
`[`| If the byte at the data pointer is zero, then instead of moving the instruction pointer forward to the next command, jump it forward to the command after the matching `]` command.
`]`| If the byte at the data pointer is nonzero, then instead of moving the instruction pointer forward to the next command, jump it back to the command after the matching `[` command.

Of note, `[` and `]` must come in matched pairs, as the input is otherwise invalid. Alright,
now that we know the grammar, let's write the parser.

## The Parser
<hr>

The parser for the language is quite compact, fitting in 10 lines. We are going
to take a quick bit to deconstruct this parser, and figure out just how it works.

```rust
#[derive(Clone)]
enum Instr {
    Left,
    Right,
    Incr,
    Decr,
    Read,
    Write,
    Loop(Vec<Self>),
}

fn parser<'a>() -> impl Parser<'a, &'a str, Vec<Instr>> {
    recursive(|bf| choice((
        just('<').to(Instr::Left),
        just('>').to(Instr::Right),
        just('+').to(Instr::Incr),
        just('-').to(Instr::Decr),
        just(',').to(Instr::Read),
        just('.').to(Instr::Write),
        bf.delimited_by(just('['), just(']')).map(Instr::Loop),
    ))
        .repeated()
        .collect())
}
```

Let's start off with the smallest bits that make up the parser: the `just(X).to(Y)`
parsers. The `just` primitive is a parser that only accepts the argument passed,
and returns it when successfully parsed. The [`to`](https://docs.rs/chumsky/latest/chumsky/trait.Parser.html#method.to)
method discards the output of the parser, and instead returns the value that
was passed to it. In the case of `just('<').to(Instr::Left)`, the value `'<'`
that is returned by [`just`](https://docs.rs/chumsky/latest/chumsky/primitive/fn.just.html)
on a successful parse is discarded, and a `Instr::Left` is returned instead.

Let's skip over the loop parsing for now, and take a quick look at [`choice`](https://docs.rs/chumsky/latest/chumsky/primitive/fn.choice.html).
This primitive receives a tuple of parsers, and returns the value returned by
the first successful parser.

Now we can look at parsing the loop. Loops can be thought of as a `[`
followed by a series of `Instr` which is followed by a `]`. Better yet, a loop
is a series of `Instr` that is surrounded by `[` and `]`. This "surrounded by"
can be solved using the [`delimited_by`](https://docs.rs/chumsky/latest/chumsky/trait.Parser.html#method.delimited_by)
method, as seen on this line:

```rust
bf.delimited_by(just('['), just(']')).map(Instr::Loop),
```

The nature of loops is recursive though, as Brainfuck allows for arbitrarily
nested loops. So, we will also need a way to define a recursive parser. Chumsky
has two ways to go about this, the simplest being the [`recursive`](https://docs.rs/chumsky/latest/chumsky/primitive/fn.recursive.html)
primitive. The parameter to [`recursive`](https://docs.rs/chumsky/latest/chumsky/primitive/fn.recursive.html)
is a closure, which receives the recursive parser itself as a parameter. In this
case `bf` represents the [`choice`](https://docs.rs/chumsky/latest/chumsky/primitive/fn.choice.html)
between the `just(X).to(Y)` parsers, and the recursive loop parser.

The final bits of the parser are the [`repeated`](https://docs.rs/chumsky/latest/chumsky/trait.Parser.html#method.repeated),
which just repeats the recursive parser until it can no longer parse an
instruction successfully and [`collect`](https://docs.rs/chumsky/latest/chumsky/trait.Parser.html#method.collect)
which similar to [`Iterator::collect`](https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.collect),
collects all of the intermediate `Instr` into a `Vec<Instr>`.

## The End
<hr>

Okay, so after that break-down and getting to gain a little bit of familiarity
with Chumsky, let's go through getting a parser going for a Language "Foo".
