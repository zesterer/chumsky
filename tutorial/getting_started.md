# Getting Started

Setting yourself up to use chumsky can be done in a few easy steps.

## Adding chumsky as a dependency

Chumsky can be added as a project dependency in one of two ways.

1) By executing the following command in your cargo project:

```sh
$ cargo add chumsky@1
```

2) By adding the following to your `Cargo.toml` file:

```toml
chumsky = "1"
```

<details>
<summary>A note about Minimum Supported Rust Versions (MSRVs)</summary>
<p>
<b>Minimum Supported Rust Version (MSRV)</b>

Chumsky currently has a MSRV of **1.65** due to internal systems that require Generic Associated Types (GATs). If you
find that chumsky fails to compile on versions of Rust later than or equal to 1.65, please
[open a bug report](https://github.com/zesterer/chumsky/issues/new).

Please note that chumsky's `nightly` feature is exempt from this minimum version requirement and may require up to and
including the latest nightly Rust compiler to work.
</p>
</details>

Back in your source code, you can use chumsky's prelude to import all commonly used types, traits, and functions.

```
use chumsky::prelude::*;
```

Alternatively, you can import whatever you need manually, but this can get rather tiresome.

The prelude contains all of the pieces you need to get started, although more complex parsers will likely need to
explicitly import less commonly used items.

## Creating a parser

Because chumsky uses typed combinators to express parsers, parser type signatures can become a little unwieldy. For this
reason, it's common practice to leave the heavy work of dealing with types to the compiler by making use of Rust's
[`impl Trait`](https://doc.rust-lang.org/stable/rust-by-example/trait/impl_trait.html) syntax.

Here's an example of a typical parser function. We'll go over what each part means.

```
//         (1)           (2)              (3)    (4)
//          |        _____|_____       ____|____  |_
fn parser<'src>() -> impl Parser<'src, &'src str, ()> {
    end() // --(5)
}
```

(**1**) Parsers are parameterised over the lifetime of their inputs. Because we don't yet know what input our parser will be
   used to parse, we declare a generic lifetime, `'src`, to allow the parser to work with whatever input lifetime it
   needs to work with.

(**2**) Because large parsers can have rather unwieldy types, we save ourselves the need to declare the exact return type
   with Rust's `impl Trait` syntax. This says to the compiler "we don't actually care what type is returned here, but
   it needs to implement the `Parser<'src, &'src, str, ()>` trait, you figure it out". Note that, unlike `dyn Trait`
   syntax, `impl Trait` has no runtime cost: the compiler simply *hides* the type from you rather than performing
   *type erasure*, which would require performing [dynamic dispatch](https://en.wikipedia.org/wiki/Dynamic_dispatch)
   while your code is running.

(**3**) The first type parameter (i.e: ignoring the lifetime parameter) of the [`Parser`] trait is the input type. Inputs
   must implement the [`Input`] trait. Examples of inputs include strings, slices, arrays, [`Stream`]s, and much more.
   For now we specify that this parser can only operate upon string slices: but it is also possible to introduce the
   input type as a generic type parameter like `I: Input<'src>` instead if you want your parser to be generic across
   more than just string slices.

(**4**) The second type parameter of the [`Parser`] trait is the output type. This is the type of the value that your parser
   will eventually give you, assuming that parsing was successful. For now, we just use an output type of [`()`], i.e:
   nothing.

(**5**) Because this is just an example parser, the implementation is composed of only a single parser primitive, [`end`].
   This is a primitive that recognises only the end of the input and generates an error if it does not find it. This
   means that our parser effectively just checks that we pass it an empty string: anything else will generate an error.

Note that this function only *creates* the parser: it does not, by itself, perform any parsing.

## Using a parser

TODO






