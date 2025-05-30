# Chumsky: A Tutorial

In this tutorial, we'll develop a parser (and interpreter!) for a programming language called 'Foo'.

Foo is a small language, but it's enough for us to have some fun. It isn't
[Turing-complete](https://en.wikipedia.org/wiki/Turing_completeness), but it is complex enough to
allow us to get to grips with parsing using Chumsky, containing many of the elements you'd find in a 'real' programming
language. Here's some sample code written in Foo:

```text
let seven = 7;
fn add x y = x + y;
add(2, 3) * -seven
```

By the end of this tutorial, you'll have an interpreter that will let you run this code, and more.

This tutorial should take somewhere between 30 and 100 minutes to complete, depending on factors such as knowledge of Rust and compiler theory.

*You can find the source code for the full interpreter in [`examples/foo.rs`](https://github.com/zesterer/chumsky/blob/main/examples/foo.rs) in the main repository.*

## Assumptions

This tutorial is here to show you how to use Chumsky: it's not a general-purpose introduction to language development as a whole. For that reason, we make a few assumptions about things you should know before jumping in:

- You should be happy reading and writing Rust. Particularly obscure syntax will be explained, but you should already be reasonably confident with concepts like functions, types, pattern matching, and error handling (`Result`, `?`, etc.).
- You should be familiar with data structures like trees and vectors.
- You should have some awareness of basic compiler theory concepts like [Abstract Syntax Trees (ASTs)](https://en.wikipedia.org/wiki/Abstract_syntax_tree), the difference between parsing and evaluation, [Backus Naur Form (BNF)](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form), etc.

## Documentation

As we go, we'll be encountering many functions and concepts from Chumsky. I strongly recommend you keep [Chumsky's documentation](https://docs.rs/chumsky/) open in another browser tab and use it to cross-reference your understanding or gain more insight into specific things that you'd like more clarification on. In particular, most of the functions we'll be using come from the [`Parser`](https://docs.rs/chumsky/latest/chumsky/trait.Parser.html) trait. Chumsky's docs include extensive doc examples for almost every function, so be sure to make use of them!

Chumsky also has [several longer examples](https://github.com/zesterer/chumsky/tree/main/examples) in the main repository: looking at these may help improve your understanding if you get stuck.

## A note on imperative vs declarative parsers

If you've tried hand-writing a parser before, you're probably expecting lots of flow control: splitting text by whitespace, matching/switching/branching on things, making a decision about whether to recurse into a function or expect another token, etc. This is an [*imperative*](https://en.wikipedia.org/wiki/Imperative_programming) approach to parser development and can be very time-consuming to write, maintain, and test.

In contrast, Chumsky parsers are [*declarative*](https://en.wikipedia.org/wiki/Declarative_programming): they still perform intricate flow control internally, but it's all hidden away so you don't need to think of it. Instead of describing *how* to parse a particular grammar, Chumsky parsers simply *describe* a grammar: and it is then Chumsky's job to figure out how to efficiently parse it.

If you've ever seen [Backus Naur Form (BNF)](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form) used to describe a language's syntax, you'll have a good sense of what this means: if you squint, you'll find that a lot of parsers written in Chumsky look pretty close to the BNF definition.

Another consequence of creating parsers in a declarative style is that *defining* a parser and *using* a parser are two different things: once created, parsers won't do anything on their own unless you give them an input to parse.

## Similarities between `Parser` and `Iterator`

The most important API in Chumsky is the [`Parser`] trait, implemented by all parsers. Because parsers don't do
anything by themselves, writing Chumsky parsers often feels very similar to writing iterators in Rust using the
[`Iterator`] trait. If you've enjoyed writing iterators in Rust before, you'll hopefully find the same satisfaction
writing parsers with Chumsky. They even [share](Parser::map) [several](IterParser::flatten)
[functions](IterParser::method.collect) with each other!

## Setting up

Create a new project with `cargo new --bin foo`, add the latest version of Chumsky as a dependency, and place
the following in your `main.rs`:

```rust ignore
use chumsky::prelude::*;

fn main() {
    let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();

    println!("{}", src);
}
```

This code has one purpose: it treats the first command-line argument as a path, reads the corresponding file,
then prints the contents to the terminal. We don't really care for handling IO errors in this tutorial, so `.unwrap()`
will suffice.

Create a file named `test.foo` and run `cargo run -- test.foo` (the `--` tells cargo to pass the remaining
arguments to the program instead of cargo itself). You should see that the contents of `test.foo`, if any, get
printed to the console.

Next, we'll create a data type that represents a program written in Foo. All programs in Foo are expressions,
so we'll call it `Expr`.

```rust ignore
#[derive(Debug)]
enum Expr<'src> {
    Num(f64),
    Var(&'src str),

    Neg(Box<Expr<'src>>),
    Add(Box<Expr<'src>>, Box<Expr<'src>>),
    Sub(Box<Expr<'src>>, Box<Expr<'src>>),
    Mul(Box<Expr<'src>>, Box<Expr<'src>>),
    Div(Box<Expr<'src>>, Box<Expr<'src>>),

    Call(&'src str, Vec<Expr<'src>>),
    Let {
        name: &'src str,
        rhs: Box<Expr<'src>>,
        then: Box<Expr<'src>>,
    },
    Fn {
        name: &'src str,
        args: Vec<&'src str>,
        body: Box<Expr<'src>>,
        then: Box<Expr<'src>>,
    }
}

```

This is Foo's [Abstract Syntax Tree](https://en.wikipedia.org/wiki/Abstract_syntax_tree) (AST). It represents
all possible Foo programs and is defined recursively in terms of itself (`Box` is used to avoid the type being
infinitely large). Each expression may itself contain sub-expressions.

As an example, the expression `let x = 5; x * 3` is encoded as follows using the `Expr` type:

```rust ignore
Expr::Let {
    name: "x",
    rhs: Box::new(Expr::Num(5.0)),
    then: Box::new(Expr::Mul(
        Box::new(Expr::Var("x")),
        Box::new(Expr::Num(3.0))
    )),
}
```

The purpose of our parser will be to perform this conversion, from source code to AST.

We're also going to create a function that creates Foo's parser. Our parser takes in a `&str` (a string slice) and
produces an `Expr`, so we'll use those types for the `I` (input) and `O` (output) type parameters.

```rust ignore
fn parser<'src>() -> impl Parser<'src, &'src str, Expr<'src>> {
    // To be filled in later...
}
```

In `main`, we'll alter the `println!` as follows:

```rust ignore
println!("{:?}", parser().parse(&src));
```

## Parsing digits

Chumsky is a 'parser combinator' library. It allows the creation of parsers by combining together many smaller
parsers. The very smallest parsers are called 'primitives' and live in the
[`primitive`](https://docs.rs/chumsky/latest/chumsky/primitive/index.html) module.

We're going to want to start by parsing the simplest element of Foo's syntax: numbers.

```rust ignore
// In `parser`...
any()
    .filter(|c: &char| c.is_ascii_digit())
```

The `any` primitive accepts any token(except the EOF) from `str`, then pass each token(a `char`) to next primitive `filter`.

The `filter` primitive allows us to read a single input and accept it if it passes a condition. In our case,
that condition simply checks that the character is a digit.

If we compile this code now, we'll encounter an error. Why?

Although we promised that our parser would produce an `Expr`, the `filter` primitive only outputs the input
it found. Right now, all we have is a parser from `str` to `char` instead of a parser from `str` to `Expr`!

To solve this, we need to crack open the 'combinator' part of parser combinators. We'll use Chumsky's `map`
method to convert the output of the parser to an `Expr`. This method is very similar to its namesake on
`Iterator`.

```rust ignore
any()
    .filter(|c: &char| c.is_ascii_digit())
    .map(|c| Expr::Num(c.to_digit(10).unwrap() as f64))
```

Here, we're converting the `char` digit to an `f64` (unwrapping is fine: `map` only gets applied to outputs
that successfully parsed!) and then wrapping it in `Expr::Num(_)` to convert it to a Foo expression.

Try running the code. You'll see that you can type a digit into `test.foo` and have our interpreter generate
an AST like so:

```rust ignore
ParseResult { output: Some(Num(5.0)), errs: [] }
```

## Parsing numbers

If you're more than a little adventurous, you'll quickly notice that typing in a multi-digit number doesn't
quite behave as expected. Inputting `42` produces a `None` output:

```rust ignore
ParseResult { output: None, errs: [EmptyErr(())] }
```

This is because by default Chumsky's parsers are NOT lazy, that means a parser will produce an error if all input is not consumed, this is what we expected for most parsers.

Combining these together, we now get an error for longer inputs. Unfortunately, this just reveals another problem
(particularly if you're working on a Unix-like platform): any whitespace before or after our digit will upset our
parser and trigger an error.

We can handle whitespace by adding a call to `padded_by` (which ignores a given pattern before and after the first)
after our digit parser, and a repeating filter for any whitespace characters.

```rust ignore
any()
    .filter(|c: &char| c.is_ascii_digit())
    .map(|c| Expr::Num(c.to_digit(10).unwrap() as f64))
    .padded_by(any().filter(|c: &char| c.is_whitespace()).repeated())
```

This example should have taught you a few important things about Chumsky's parsers:

1. Parsers are NOT lazy: all input must be consumed
2. Whitespace is not automatically ignored. Chumsky is a general-purpose parsing library, and some languages care very much about the structure of whitespace, so Chumsky does too

## Cleaning up and taking shortcuts

At this point, things are starting to look a little messy. We've ended up writing 4 lines of code to properly parse a single digit. Let's clean things up a bit. We'll also make use of a bunch of text-based parser primitives that come with Chumsky to get rid of some of this cruft.

```rust ignore
text::int(10)
    .map(|s: &str| Expr::Num(s.parse().unwrap()))
    .padded()
```

`text::int(10)` accepts any number of decimal integers (`10` is the base); `map` is still used but now our parser can
parse multi-digit integers, so the output type it's mapping is `&str`, not `char`; `padded` is a shortcut for ignoring
any leading or trailing whitespace, just like our more manual code did.

That's better. We've also swapped out our custom digit parser with a built-in parser that parses any non-negative integer.

## Evaluating simple expressions

We'll now take a diversion away from the parser to create a function that can evaluate our AST. This is the 'heart' of
our interpreter and is the thing that actually performs the computation of programs.

```rust ignore
fn eval<'src>(expr: &'src Expr<'src>) -> Result<f64, String> {
    match expr {
        Expr::Num(x) => Ok(*x),
        Expr::Neg(a) => Ok(-eval(a)?),
        Expr::Add(a, b) => Ok(eval(a)? + eval(b)?),
        Expr::Sub(a, b) => Ok(eval(a)? - eval(b)?),
        Expr::Mul(a, b) => Ok(eval(a)? * eval(b)?),
        Expr::Div(a, b) => Ok(eval(a)? / eval(b)?),
        _ => todo!(), // We'll handle other cases later
    }
}
```

This function might look scary at first glance, but there's not too much going on here: it just recursively calls
itself, evaluating each node of the AST, combining the evaluated output via operators, until it has a final result. Any
runtime errors simply get thrown back down the stack using `?`.

We'll also change our `main` function a little so that we can pass our AST to `eval`.

```rust ignore
fn main() {
    let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();

    match parser().parse(&src).into_result() {
        Ok(ast) => match eval(&ast) {
            Ok(output) => println!("{}", output),
            Err(eval_err) => println!("Evaluation error: {}", eval_err),
        },
        Err(parse_errs) => parse_errs
            .into_iter()
            .for_each(|e| println!("Parse error: {}", e)),
    }
}
```

This also looks like a big change, but it's mostly just an extension of the previous code to pass the AST on to `eval`
if parsing is successful. If unsuccessful, we just print the errors generated by the parser. Right now, none of our
operators can produce errors when evaluated, but this will change in the future so we make sure to handle them in
preparation.

## Parsing unary operators

Jumping back to our parser, let's handle unary operators. Currently, our only unary operator is `-`, the negation
operator. We're looking to parse any number of `-`, followed by a number. More formally:

```text
expr = op* + int
```

We'll also give our `int` parser a new name, `atom`, for reasons that will become clear later.

```rust ignore
let int = text::int(10)
    .map(|s: &str| Expr::Num(s.parse().unwrap()))
    .padded();

let atom = int;

let op = |c| just(c).padded();

let unary = op('-')
    .repeated()
    .foldr(atom, |_op, rhs| Expr::Neg(Box::new(rhs)));

unary
```

Here, we meet a few new combinators:

- `just` defines a parser that accepts only the given input. We leverage it to define `op` that can easily construct
an operator parser later by passing the operator character.

- `repeated` will parse a given pattern any number of times (including zero!). It also implements [`IterParser`], a
parser that generates many sequential outputs.

- `foldr` means "fold-right". It is a method on [`IterParser`] that takes each element of the iterating parser, and the
output of a final terminating parser, then 'folds' them all into a single value by repeatedly applying the given
closure. The first argument `atom` is the terminating parser.

This is worth a little more consideration. We're trying to parse *any number* of negation operators, followed by a
single atom (for now, just a number). For example, the input `---42` would generate the following outputs to be
processed by `foldr`:

```rust ignore
['-', '-', '-'], Num(42.0)
```

The `foldr` combinator repeatedly applies the folding function to 'fold' the elements into a single element, like so:

```text
(['-',   '-',   '-'],   Num(42.0))
  ---    ---    ---     ---------
   |      |      |           |
   |      |       \         /
   |      |      Neg(Num(42.0))
   |      |            |
   |       \          /
   |    Neg(Neg(Num(42.0)))
   |            |
    \          /
Neg(Neg(Neg(Num(42.0))))
```

This may be a little hard to conceptualise for those used to imperative programming, but for functional programmers it
should come naturally: [`fold`](https://en.wikipedia.org/wiki/Fold_(higher-order_function)) is a function that appears
in many functional languages, and even [in Rust's iterator
API](https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.fold)!

Give the interpreter a try. You'll be able to enter inputs as before, but also values like `-17`. You can even apply
the negation operator multiple times: `--9` will yield a value of `9` in the command line.

This is exciting: we've finally started to see our interpreter perform useful (sort of) computations!

## Parsing binary operators

Let's keep the momentum going and move over to binary operators. Traditionally, these pose quite a problem for
parsers. To parse an expression like `3 + 4 * 2`, it's necessary to understand that multiplication
[binds more eagerly than addition](https://en.wikipedia.org/wiki/Order_of_operations) and hence is applied first.
Therefore, the result of this expression is `11` and not `14`.

Parsers employ a range of strategies to handle these cases, but for Chumsky things are simple: the most eagerly binding
(highest 'precedence') operators should be those that get considered first when parsing.

It's worth noting that summation operators (`+` and `-`) are typically considered to have the *same* precedence as
one-another. The same also applies to product operators (`*` and `/`). For this reason, we treat each group as a single
pattern.

At each stage, we're looking for a simple pattern: an unary expression, following by any number of a combination of an
operator and an unary expression. More formally:

```text
expr = unary + (op + unary)*
```

Let's expand our parser.

```rust ignore
let int = text::int(10)
    .map(|s: &str| Expr::Num(s.parse().unwrap()))
    .padded();

let atom = int;

let op = |c| just(c).padded();

let unary = op('-')
    .repeated()
    .foldr(atom, |_op, rhs| Expr::Neg(Box::new(rhs)));

let product = unary.foldl(
    choice((
        op('*').to(Expr::Mul as fn(_, _) -> _),
        op('/').to(Expr::Div as fn(_, _) -> _),
    ))
    .then(unary)
    .repeated(),
    |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
);

let sum = product.foldl(
    choice((
        op('+').to(Expr::Add as fn(_, _) -> _),
        op('-').to(Expr::Sub as fn(_, _) -> _),
    ))
    .then(product)
    .repeated(),
    |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
);

sum
```

The `Expr::Mul as fn(_, _) -> _` syntax might look a little unfamiliar, but don't worry! In Rust,
[tuple enum variants are implicitly functions](https://stackoverflow.com/questions/54802045/what-is-this-strange-syntax-where-an-enum-variant-is-used-as-a-function).
All we're doing here is making sure that Rust treats each of them as if they had the same type using the `as` cast, and
then letting type inference do the rest. Those functions then get passed through the internals of the parser and end up
in `op` within the `foldl` call.

Another three combinators are introduced here:

- `choice` attempts each parser in a tuple, producing the output of the first to successfully parse

- `to` is similar to `map`, but instead of mapping the output, entirely overrides the output with a new value. In our
  case, we use it to convert each binary operator to a function that produces the relevant AST node for that operator.

- `foldl` is very similar to `foldr` in the last section but, instead of parsing many leading patterns and then a
  single terminating pattern, it parses a single starting pattern and then main trailing patterns.

In a similar manner to `foldr` in the previous section on unary expressions, `foldl` is used to fold chains of binary
operators into a single expression tree. For example, the input `2 + 3 - 7 + 5` would generate the following input to
`foldl`:

```rust ignore
Num(2.0), [(Expr::Add, Num(3.0)), (Expr::Sub, Num(7.0)), (Add, Num(5.0))]
```

This then gets folded together by `foldl` like so:

```text
Num(2.0),   [(Add, Num(3.0)),   (Sub, Num(7.0)),   (Add, Num(5.0))])
--------     ---------------     --------------    ---------------
   |                |                 |                  |
    \              /                  |                  |
Add(Num(2.0), Num(3.0))               |                  |
           |                          |                  |
            \                        /                   |
     Sub(Add(Num(2.0), Num(3.0)), Num(7.0))              |
                      |                                  |
                       \                                /
              Add(Sub(Add(Num(2.0), Num(3.0)), Num(7.0)), Num(5.0))
```

Give the interpreter a try. You should find that it can correctly handle both unary and binary operations combined in
arbitrary configurations, correctly handling precedence. You can use it as a pocket calculator!

## Parsing parentheses

A new challenger approaches: *nested expressions*. Sometimes, we want to override the default operator precedence rules
entirely. We can do this by nesting expressions within parentheses, like `(3 + 4) * 2`. How do we handle this?

The creation of the `atom` pattern a few sections before was no accident: parentheses have a greater precedence than
any operator, so we should treat a parenthesized expression as if it were equivalent to a single value. We call things
that behave like single values 'atoms' by convention.

We're going to hoist our entire parser up into a [`recursive()`] parser, allowing us to define it in terms of itself.

```rust ignore
recursive(|expr| {
    let int = text::int(10).map(|s: &str| Expr::Num(s.parse().unwrap()));

    let atom = int.or(expr.delimited_by(just('('), just(')'))).padded();

    let op = |c| just(c).padded();

    let unary = op('-')
        .repeated()
        .foldr(atom, |_op, rhs| Expr::Neg(Box::new(rhs)));

    let product = unary.clone().foldl(
        choice((
            op('*').to(Expr::Mul as fn(_, _) -> _),
            op('/').to(Expr::Div as fn(_, _) -> _),
        ))
        .then(unary)
        .repeated(),
        |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
    );

    let sum = product.clone().foldl(
        choice((
            op('+').to(Expr::Add as fn(_, _) -> _),
            op('-').to(Expr::Sub as fn(_, _) -> _),
        ))
        .then(product)
        .repeated(),
        |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
    );

    sum
})
```

There are a few things worth paying attention to here.

1. `or` attempts to parse a pattern and, if unsuccessful, instead attempts another pattern

2. `recursive` allows us to define a parser recursively in terms of itself by giving us a copy of it within the
   closure's scope

3. We use the recursive definition of `expr` within the definition of `atom`. We use the new `delimited_by` combinator
   to allow it to sit nested within a pair of parentheses

4. We have to clone `unary` and `product` to use them in the closure of `recursive`

Try running the interpreter. You'll find that it can handle a surprising number of cases elegantly. Make sure that the
following cases work correctly:

| Expression    | Expected result |
|---------------|-----------------|
| `3 * 4 + 2`   | `14`            |
| `3 * (4 + 2)` | `18`            |
| `-4 + 2`      | `-2`            |
| `-(4 + 2)`    | `-6`            |

## Parsing lets

Our next step is to handle `let`. Unlike Rust and other imperative languages, `let` in Foo is an expression and not an
statement (Foo has no statements) that takes the following form:

```ignore
let <ident> = <expr>; <expr>
```

We only want `let`s to appear at the outermost level of the expression, so we leave it out of the original recursive
expression definition. However, we also want to be able to chain `let`s together, so we put them in their own recursive
definition. We call it `decl` ('declaration') because we're eventually going to be adding `fn` syntax too.

```rust ignore
let ident = text::ascii::ident().padded();

let expr = recursive(|expr| {
    let int = text::int(10).map(|s: &str| Expr::Num(s.parse().unwrap()));

    let atom = int
        .or(expr.delimited_by(just('('), just(')')))
        .or(ident.map(Expr::Var))
        .padded();

    let op = |c| just(c).padded();

    let unary = op('-')
        .repeated()
        .foldr(atom, |_op, rhs| Expr::Neg(Box::new(rhs)));

    let product = unary.clone().foldl(
        choice((
            op('*').to(Expr::Mul as fn(_, _) -> _),
            op('/').to(Expr::Div as fn(_, _) -> _),
        ))
        .then(unary)
        .repeated(),
        |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
    );

    let sum = product.clone().foldl(
        choice((
            op('+').to(Expr::Add as fn(_, _) -> _),
            op('-').to(Expr::Sub as fn(_, _) -> _),
        ))
        .then(product)
        .repeated(),
        |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
    );

    sum
});

let decl = recursive(|decl| {
    let r#let = text::ascii::keyword("let")
        .ignore_then(ident)
        .then_ignore(just('='))
        .then(expr.clone())
        .then_ignore(just(';'))
        .then(decl)
        .map(|((name, rhs), then)| Expr::Let {
            name,
            rhs: Box::new(rhs),
            then: Box::new(then),
        });

    r#let
        // Must be later in the chain than `r#let` to avoid ambiguity
        .or(expr)
        .padded()
});

decl
```

`keyword` is simply a parser that looks for an exact identifier (i.e: it doesn't match identifiers that only start with
a keyword).

Other than that, there's nothing in the definition of `r#let` that you haven't seen before: familiar combinators, but
combined in different ways. `ignore_then` and `then_ignore` are used to ignore parts of the surface syntax (like
keywords) that we don't care about representing in the AST.

Another thing to note is that the definition of `ident` will parse `"let"`. To avoid the parser accidentally deciding
that `"let"` is a variable, we place `r#let` earlier in the or chain than `expr` so that it priorities the correct
interpretation. As mentioned in previous sections, Chumsky handles ambiguity simply by choosing the first successful
parse it encounters, so making sure that we declare things in the right order can sometimes be important. A
fully-fledged 'production-worthy' parser might want to separate lexing and parsing into distinct steps to avoid
accidental ambiguity such as this, but for now we'll keep going with our 'larser' design (i.e: lexing and parsing as a
single step).

You should now be able to run the interpreter and have it accept inputs such as:

```ignore
let five = 5;
five * 3
```

Unfortunately, the `eval` function will panic because we've not yet handled `Expr::Var` or `Expr::Let`. Let's do that
now.

```rust ignore
fn eval<'src>(expr: &'src Expr<'src>, vars: &mut Vec<(&'src str, f64)>) -> Result<f64, String> {
    match expr {
        Expr::Num(x) => Ok(*x),
        Expr::Neg(a) => Ok(-eval(a, vars)?),
        Expr::Add(a, b) => Ok(eval(a, vars)? + eval(b, vars)?),
        Expr::Sub(a, b) => Ok(eval(a, vars)? - eval(b, vars)?),
        Expr::Mul(a, b) => Ok(eval(a, vars)? * eval(b, vars)?),
        Expr::Div(a, b) => Ok(eval(a, vars)? / eval(b, vars)?),
        Expr::Var(name) => {
            if let Some((_, val)) = vars.iter().rev().find(|(var, _)| var == name) {
                Ok(*val)
            } else {
                Err(format!("Cannot find variable `{}` in scope", name))
            }
        }
        Expr::Let { name, rhs, then } => {
            let rhs = eval(rhs, vars)?;
            vars.push((name, rhs));
            let output = eval(then, vars);
            vars.pop();
            output
        }
        _ => todo!(),
    }
}
```

Woo! That got a bit more complicated. Don't fear, there are only 3 important changes:

1. Because we need to keep track of variables that were previously defined, we use a `Vec` to remember them. Because
   `eval` is a recursive function, we also need to pass is to all recursive calls.

2. When we encounter an `Expr::Let`, we first evaluate the right-hand side (`rhs`). Once evaluated, we push it to the
   `vars` stack and evaluate the trailing `then` expression (i.e: all of the remaining code that appears after the
   semicolon). Popping it afterwards is not *technically* necessary because Foo does not permit nested declarations,
   but we do it anyway because it's good practice and it's what we'd want to do if we ever decided to add nesting.

3. When we encounter an `Expr::Var` (i.e: an inline variable) we search the stack *backwards* (because Foo permits
   [variable shadowing](https://en.wikipedia.org/wiki/Variable_shadowing) and we only want to find the most recently
   declared variable with the same name) to find the variable's value. If we can't find a variable of that name, we
   generate a runtime error which gets propagated back up the stack.

Obviously, the signature of `eval` has changed so we'll update the call in `main` to become:

```rust ignore
eval(&ast, &mut Vec::new())
```

Make sure to test the interpreter. Try experimenting with `let` declarations to make sure things aren't broken. In
particular, it's worth testing variable shadowing by ensuring that the following program produces `8`:

```ignore
let x = 5;
let x = 3 + x;
x
```

## Parsing functions

We're almost at a complete implementation of Foo. There's just one thing left: *functions*.

Surprisingly, parsing functions is the easy part. All we need to modify is the definition of `decl` to add `r#fn`. It
looks very much like the existing definition of `r#let`:

```rust ignore
let decl = recursive(|decl| {
    let r#let = text::ascii::keyword("let")
        .ignore_then(ident)
        .then_ignore(just('='))
        .then(expr.clone())
        .then_ignore(just(';'))
        .then(decl.clone())
        .map(|((name, rhs), then)| Expr::Let {
            name,
            rhs: Box::new(rhs),
            then: Box::new(then),
        });

    let r#fn = text::ascii::keyword("fn")
        .ignore_then(ident)
        .then(ident.repeated().collect::<Vec<_>>())
        .then_ignore(just('='))
        .then(expr.clone())
        .then_ignore(just(';'))
        .then(decl)
        .map(|(((name, args), body), then)| Expr::Fn {
            name,
            args,
            body: Box::new(body),
            then: Box::new(then),
        });

    r#let.or(r#fn).or(expr).padded()
});
```

The only thing to note here is the use of `repeated()`, which gives us an [`IterParser`]. To collect this iterable
parser's elements into a vector, we use [`IterParser::collect`].

Obviously, we also need to add support for *calling* functions by modifying `atom`:

```rust ignore
 let call = ident
    .then(
        expr.clone()
            .separated_by(just(','))
            .allow_trailing()   // Foo is Rust-like, so allow trailing commas to appear in arg lists
            .collect::<Vec<_>>()
            .delimited_by(just('('), just(')')),
    )
    .map(|(f, args)| Expr::Call(f, args));

let atom = int
    .or(expr.delimited_by(just('('), just(')')))
    .or(call)
    .or(ident.map(Expr::Var))
    .padded();
```

The only new combinator here is `separated_by` which behaves like `repeated`, but requires a separator pattern between
each element. It has a method called `allow_trailing` which allows for parsing a trailing separator at the end of the
elements.

Next, we modify our `eval` function to support a function stack.

```rust ignore
fn eval<'src>(
    expr: &'src Expr<'src>,
    vars: &mut Vec<(&'src str, f64)>,
    funcs: &mut Vec<(&'src str, &'src [&'src str], &'src Expr<'src>)>,
) -> Result<f64, String> {
    match expr {
        Expr::Num(x) => Ok(*x),
        Expr::Neg(a) => Ok(-eval(a, vars, funcs)?),
        Expr::Add(a, b) => Ok(eval(a, vars, funcs)? + eval(b, vars, funcs)?),
        Expr::Sub(a, b) => Ok(eval(a, vars, funcs)? - eval(b, vars, funcs)?),
        Expr::Mul(a, b) => Ok(eval(a, vars, funcs)? * eval(b, vars, funcs)?),
        Expr::Div(a, b) => Ok(eval(a, vars, funcs)? / eval(b, vars, funcs)?),
        Expr::Var(name) => {
            if let Some((_, val)) = vars.iter().rev().find(|(var, _)| var == name) {
                Ok(*val)
            } else {
                Err(format!("Cannot find variable `{}` in scope", name))
            }
        }
        Expr::Let { name, rhs, then } => {
            let rhs = eval(rhs, vars, funcs)?;
            vars.push((*name, rhs));
            let output = eval(then, vars, funcs);
            vars.pop();
            output
        }
        Expr::Call(name, args) => {
            if let Some((_, arg_names, body)) =
                funcs.iter().rev().find(|(var, _, _)| var == name).copied()
            {
                if arg_names.len() == args.len() {
                    let mut args = args
                        .iter()
                        .map(|arg| eval(arg, vars, funcs))
                        .zip(arg_names.iter())
                        .map(|(val, name)| Ok((*name, val?)))
                        .collect::<Result<_, String>>()?;
                    let old_vars = vars.len();
                    vars.append(&mut args);
                    let output = eval(body, vars, funcs);
                    vars.truncate(old_vars);
                    output
                } else {
                    Err(format!(
                        "Wrong number of arguments for function `{}`: expected {}, found {}",
                        name,
                        arg_names.len(),
                        args.len(),
                    ))
                }
            } else {
                Err(format!("Cannot find function `{}` in scope", name))
            }
        }
        Expr::Fn {
            name,
            args,
            body,
            then,
        } => {
            funcs.push((name, args, body));
            let output = eval(then, vars, funcs);
            funcs.pop();
            output
        }
    }
}
```

Another big change! On closer inspection, however, this looks a lot like the change we made previously when we added
support for `let` declarations. Whenever we encounter an `Expr::Fn`, we just push the function to the `funcs` stack and
continue. Whenever we encounter an `Expr::Call`, we search the function stack backwards, as we did for variables, and
then execute the body of the function (making sure to evaluate and push the arguments!).

As before, we'll need to change the `eval` call in `main` to:

```rust ignore
eval(&ast, &mut Vec::new(), &mut Vec::new())
```

Give the interpreter a test - see what you can do with it! Here's an example program to get you started:

```ignore
let five = 5;
let eight = 3 + five;
fn add x y = x + y;
add(five, eight)
```

## Full source code

You can find the full source code for Foo [in the crate
examples](https://github.com/zesterer/chumsky/blob/main/examples/foo.rs).

## Conclusion

Here ends our exploration into Chumsky's API. We only scratched the surface of what Chumsky can do, but now you'll need
to rely on the examples in the repository and the API doc examples for further help. Nonetheless, I hope it was an
interesting foray into the use of parser combinators for the development of parsers.

If nothing else, you've now got a neat little calculator language to play with.

Interestingly, there is a subtle bug in Foo's `eval` function that produces unexpected scoping behaviour with function
calls. I'll leave finding it as an exercise for the reader.

## Extension tasks

- Find the interesting function scoping bug and consider how it could be fixed

- Split token lexing into a separate compilation stage to avoid the need for `.padded()` in the parser

- Add more operators

- Add an `if <expr> then <expr> else <expr>` ternary operator

- Add values of different types by turning `f64` into an `enum`

- Add lambdas to the language

- Format the error message in a more useful way, perhaps by providing a reference to the original code
