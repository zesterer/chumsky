# Getting Started

Setting yourself up to use chumsky can be done in a few easy steps.

- [Adding chumsky as a dependency](#adding-chumsky-as-a-dependency)

- [Creating parsers](#creating-parsers)

- [Using parsers](#using-parsers)

- [Advice](#advice)

    - [Compiler errors](#compiler-errors)

    - [Compilation times](#compilation-times)

    - [Debugging parsers](#debugging-parsers)

## Adding chumsky as a dependency

Chumsky can be added as a project dependency in one of two ways.

1) By executing the following command in your cargo project:

```sh
$ cargo add chumsky
```

2) By adding the following to your `Cargo.toml` file:

```toml
chumsky = "0.10"
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

## Creating parsers

Because chumsky uses typed combinators to express parsers, parser type signatures can become a little unwieldy. For this
reason, it's common practice to leave the heavy work of dealing with types to the compiler by making use of Rust's
[`impl Trait`](https://doc.rust-lang.org/stable/rust-by-example/trait/impl_trait.html) syntax.

Here's an example of a typical parser function. We'll go over what each part means.

```
# use chumsky::prelude::*;
//        (1)            (2)              (3)    (4)
//        _|__       _____|_____       ____|____  |_
fn parser<'src>() -> impl Parser<'src, &'src str, ()> {
    end() // --(5)
}
```

1. Parsers are parameterised over the lifetime of their inputs. Because we don't yet know what input our parser will be
   used to parse, we declare a generic lifetime, `'src`, to allow the parser to work with whatever input lifetime it
   needs to work with.

2. Because large parsers can have rather unwieldy types, we save ourselves the need to declare the exact return type
   with Rust's `impl Trait` syntax. This says to the compiler "we don't actually care what type is returned here, but
   it needs to implement the `Parser<'src, &'src, str, ()>` trait, you figure it out". Note that, unlike `dyn Trait`
   syntax, `impl Trait` has no runtime cost: the compiler simply *hides* the type from you rather than performing
   *type erasure*, which would require performing [dynamic dispatch](https://en.wikipedia.org/wiki/Dynamic_dispatch)
   while your code is running.

3. The first type parameter (i.e: ignoring the lifetime parameter) of the [`Parser`] trait is the input type. Inputs
   must implement the [`Input`] trait. Examples of inputs include strings, slices, arrays, [`Stream`]s, and much more.
   For now we specify that this parser can only operate upon string slices: but it is also possible to introduce the
   input type as a generic type parameter like `I: Input<'src>` instead if you want your parser to be generic across
   more than just string slices.

4. The second type parameter of the [`Parser`] trait is the output type. This is the type of the value that your parser
   will eventually give you, assuming that parsing was successful. For now, we just use an output type of `()`, i.e:
   nothing.

5. Because this is just an example parser, the implementation is just a single parser primitive, [`end`]. This is a
   primitive that recognises only the end of the input and generates an error if it does not find it. This means that
   our parser effectively just checks that we pass it an empty string: anything else will generate an error.

Note that this function only *creates* the parser: it does not, by itself, perform any parsing.

## Using parsers

It's all very well creating parsers but in order to write useful programs, we need to invoke them. Chumsky provides
several functions for this, but the main two are:

- [`Parser::parse`]: parses an input, generating an output value and/or any errors that were encountered along the way

- [`Parser::check`]: checks that an input is valid, generating any errors that were encountered along the way

Both functions give us back a [`ParseResult`]. You can think of this sort of like Rust's regular [`Result`] type, except
it allows both outputs and errors to be generated at the same time (although we won't yet use this functionality). If
you just want parsing to be an all-or-nothing affair, you can use [`ParseResult::into_result`] to convert this into a
regular [`Result`].

Let's write some tests for the parser we wrote in the last section.

```
# use chumsky::prelude::*;
# fn parser<'src>() -> impl Parser<'src, &'src str, ()> { end() }
#[test]
fn test_parser() {
    // Our parser expects empty strings, so this should parse successfully
    assert_eq!(parser().parse("").into_result(), Ok(()));

    // Anything other than an empty string should produce an error
    assert!(parser().parse("123").has_errors());
}
```

Hopefully, this code is fairly self-explanatory. We call `parser()` (the function we wrote in the previous section) to
create an instance of our parser, and then we call [`Parser::parse`] on it with the desired input to actually do some
parsing. The return value is the result of the parse.

From here, the world is your lobster: you can move on to the tutorial sections of this guide or you can jump write into
writing parsers. The main repository has [plenty of examples](https://github.com/zesterer/chumsky/tree/main/examples)
to use as a reference and the crate has documentation that will help guide you, with many examples.

## Advice

Chumsky is a powerful crate with a lot of bells and whistles. It makes sense that there also a lot of ways things can go
wrong too.

### Compiler errors

Chumsky is a combinator crate and leans heavily into Rust's type system (traits, generics, etc.) in order to combine
high performance and ergonomics. Unfortunately, the Rust compiler can still struggle to generate useful error messages
for large chumsky parsers (although things have improved substantially in recent releases!). When you hit a compiler
error you're struggling to understand, you should:

1. Always solve the first error that Rust generates. Rust generates errors in the order that it finds them, so the first
   error is usually reliably accurate while later errors tend to get increasingly speculative as the compiler needs to
   make more and more assumptions about your program to handle prior errors. This often results in many additional
   'phantom errors': errors that muddy the water and make it look like the problem is more complicated to solve than it
   actually is.

2. Reduce the size of types. Thankfully Rust has recently taken steps to avoid printing extremely long type signatures
   out to the terminal. Even so, parser types can still be rather large. You can reduce this problem by commenting out
   unnecessary parts of your parser, or using `.simplify()` on parsers that contribute to the error to simplify their
   types.

3. Complaints about types 'not implementing [`Parser`]' are more often than not a failure to fulfil the obligations that
   come with implementing the trait. For example, [`recursive()`] requires that the inner parser implements `Clone`: a
   parser that doesn't (because, say, you moved a non-cloneable type into the closure) can't be used with
   [`recursive()`] and so Rust will translate this, in its parlance, to the type not implementing [`Parser`].

### Compilation times

Chumsky's heavy use of Rust's type system can result in parsers taking some time to compile. In particular, a common
cause of long compilation times are long chains of [`Parser::or`], which sadly tend to produce exponential behaviour in
Rust's trait solver.

**Don't fear! There are solutions.**

1. Replace long (more than a handful of cases) [`Parser::or`] chains with [`choice`], which has identical behaviour but
   gives Rust's trait solver a much easier time.

2. Use [`Parser::boxed`] at the end of longer parser chains to perform type erasure, thereby reducing the amount of work
   Rust needs to do to understand your parser. If you've been using Rust for a while, your first intention might be to
   feel nauseous as such a suggestion: "*allocation?* In *my* high-performance code? *No thanks*". However, remember
   that this allocation only occurs on parser *creation*, not during the parsing process. A few strategically placed
   `.boxed()` calls has almost no effect on parsing performance (modern CPU branch predictors have absolutely no trouble
   eliminating their cost), and in fact can sometimes *improve* performance!

### Debugging parsers

TODO
