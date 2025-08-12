# Recursion

Most non-trivial languages - both spoken and programmed - are *recursive*. Grammars that describe these languages can
express recursion by having a term in the language contain itself (either directly or indirectly). Noam Chomsky
believed that recursion was *so* fundamental to human language that he considered it the primary demarcation between
human and non-human language. This is debated in academic circles, but chumsky treats recursion with similar reverance.

## The Problem

In Rust, writing a recursive function is usually trivial.

```rust
fn factorial(x: u32) -> u32 {
    if x <= 1 {
        1
    } else {
        x * factorial(x - 1)
    }
}
```

However, chumsky parsers are *values*, not *functions*. Just like [`Iterator`]s, they can be moved around, manipulated,
and invoked in a lazy manner. Intuitively, we might think to write a recursive parser to parse `4 + (1 + 2) + 3` like so:

```rust compile_fail
use chumsky::prelude::*;

fn a_parser<'src>() -> impl Parser<'src, &'src str, i32> + Clone {
    let int = text::int(10).map(|s: &str| s.parse().unwrap());

    let atom = choice((
        int,
        a_parser().delimited_by(just('('), just(')')),
    ))
        .padded();

    atom.clone().foldl(
        just('+').padded().ignore_then(atom).repeated(),
        |lhs, rhs| lhs + rhs,
    )
}
```

Unfortunately, we hit an error:

```text
error[E0720]: cannot resolve opaque type
   --> recursion.rs:1:24
    |
 1  |   fn a_parser<'src>() -> impl Parser<'src, &'src str, i32> + Clone {
    |                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ recursive opaque type
...
 9  | /     atom.clone().foldl(
10  | |         just('+').padded().ignore_then(atom).repeated(),
11  | |         |lhs, rhs| lhs + rhs,
12  | |     )
    | |     -
    | |_____|
    | |_____returning here with type `...`
```

We can 'solve' this problem by boxing `a_parser()`, but all it does is convert the compilation error into a run-time
stack overflow. Why? The answer, if we take a step back, should be obvious: our `a_parser` function isn't actually
doing any parsing, it's just *creating* a parser. In order to create a parser, it needs to call itself... which means
calling itself again... forever. We've created infinite recursion. No dice.

## A Solution

To get us out of this somewhat sticky bind, chumsky provides a special combinator called `recursive`. It allows us to
refer to a parser within its own definition - without getting us caught in recursive hot water.

```rust
use chumsky::prelude::*;

fn a_parser<'src>() -> impl Parser<'src, &'src str, i32> {
    recursive(|a_parser| {
        let int = text::int(10).map(|s: &str| s.parse().unwrap());

        let atom = choice((
            int,
            a_parser.delimited_by(just('('), just(')')),
        ))
            .padded();

        atom.clone().foldl(
            just('+').padded().ignore_then(atom).repeated(),
            |lhs, rhs| lhs + rhs,
        )
    })
}
```

Notice how our `a_parser` function is no longer recursive: instead, we get the definition of `a_parser` from the
closure parameter.

## More Complicated Cases

More complicated parsers tend to have many mutually-recursive patterns. For example, in Rust's syntax, the 'expression'
and 'type' terms are intertwined: expressions can contain types (in the form of
[turbofish](https://techblog.tonsser.com/posts/what-is-rusts-turbofish) type annotations, or in `as` casts) and types
can contain expressions (in array type sizes or in const generics).

It is possible to use `recursive` in a 'nested' manner to express such a thing, but chumsky provides a simpler
solution:
[`Recursive::declare`] and [`Recursive::define`]. These functions allow us to *entirely* decouple the declaration and
definition of a recursive parser, giving us the ability to easily declare our mutually-recursive parsers up-front and
then use them in each other's definitions.
