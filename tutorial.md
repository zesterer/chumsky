# Chumsky: A Tutorial

*Please note that this tutorial is kept up to date with the `master` branch and not the most stable release: small
details may differ!*

In this tutorial, we'll develop a parser (and interpreter!) for a simple programming language called 'Foo'.

Foo is a simple language, but it's enough for us to have some fun. It isn't
[Turing-complete](https://en.wikipedia.org/wiki/Turing_completeness), but it is complex enough to
allow us to get to grips with parsing using Chumsky. Here's some sample code from Foo:

```
let seven = 7;
fn add x y = x + y;
add(2, 3) * -seven
```

## Setting up

Create a new project with `cargo new --bin foo`, add the latest version of Chumsky as a dependency, and place
the following in your `main.rs`:

```rust
use chumsky::prelude::*;

fn main() {
    let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();

    println!("{}", src);
}
```

This code is quite simple: it treats the first command-line argument as a path, reads the corresponding file,
then prints the contents to the terminal.

Create a file named `test.foo` and run `cargo run -- test.foo` (the `--` tells cargo to pass the remaining
arguments to the program instead of cargo itself). You should see that the contents of `test.foo`, if any, get
printed to the console.

Next, we'll create a data type that represents a program written in Foo. All programs in Foo are expressions,
so we'll call it `Expr`.

```rust
#[derive(Debug)]
enum Expr {
    Num(f64),
    Var(String),

    Neg(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),

    Let {
        name: String,
        rhs: Box<Expr>,
        then: Box<Expr>,
    },
    Fn {
        name: String,
        args: Vec<String>,
        rhs: Box<Expr>,
        then: Box<Expr>,
    },
}
```

This is Foo's [Abstract Syntax Tree](https://en.wikipedia.org/wiki/Abstract_syntax_tree) (AST). It represents
all possible Foo programs and is defined recursively in terms of itself (`Box` is used to avoid the type being
infinitely large). Each expression may itself contain sub-expressions.

We're also going to create a function that creates Foo's parser. Our parser takes in a `char` stream and
produces an `Expr`, so we'll use those types for the `I` (input) and `O` (output) type parameters.

```rust
fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    // To be filled in later...
}
```

The `Error` associated type allows us to customise the error type that Chumsky uses. For now, we'll stick to
`Simple<I>`, a built-in error type that does everything we need.

In `main`, we'll alter the `println!` as follows:

```rust
println!("{:?}", parser().parse(src));
```

## Parsing digits

Chumsky is a 'parser combinator' library. It allows the creation of parsers by combining together many smaller
parsers. The very smallest parsers are called 'primitives' and live in the
[`primitive`](https://docs.rs/chumsky/latest/chumsky/primitive/index.html) module.

We're going to want to start by parsing the simplest element of Foo's syntax: numbers.

```rust
// In `parser`...
filter(|c: &char| c.is_ascii_digit())
```

The `filter` primitive allows us to read a single input and accept it if it passes a condition. In our case,
that condition simply checks that the character is a digit.

If we compile this code now, we'll encounter an error. Why?

Although we promised that our parser would produce an `Expr`, the `filter` primitive only outputs the input
it found. Right now, all we have is a parser from `char` to `char` instead of a parser from `char` to `Expr`!

To solve this, we need to crack open the 'combinator' part of parser combinators. We'll use Chumsky's `map`
method to convert the output of the parser to an `Expr`. This method is very similar to its namesake on
`Iterator`.

```rust
filter(|c: &char| c.is_ascii_digit())
    .map(|c| Expr::Num(c.to_digit(10).unwrap() as f64))
```

Here, we're converting the `char` digit to an `f64` (unwrapping is fine: `map` only gets applied to outputs
that successfully parsed!) and then wrapping it in `Expr::Num(_)` to convert it to a Foo expression.

Try running the code. You'll see that you can type a digit into `test.foo` and have our interpreter generate
an AST like so:

```
Ok(Num(5.0))
```

## Parsing numbers

If you're more than a little adventurous, you'll quickly notice that typing in a multi-digit number doesn't
quite behave as expected. Inputting `42` will only produce a `Num(4.0)` AST.

This is because `filter` only accepts a *single* input. But now another question arises: why did our interpreter
*not* complain at the trailing digits that didn't get parsed?

The answer is that Chumsky's parsers are *lazy*: they will consume all of the input that they can and then stop.
If there's any trailing input, it'll be ignored.

This is obviously not always desirable. If the user places random nonsense at the end of the file, we want to be
able to generate an error about it! Worse still, that 'nonsense' could be input the user intended to be part of
the program, but that contained a syntax error and so was not properly parsed. How can we force the parser to consume
all of the input?

To do this, we can make use of two new parsers: the `then_ignore` combinator and the `end` primitive.

```rust
filter(|c: &char| c.is_ascii_digit())
    .map(|c| Expr::Num(c.to_digit(10).unwrap() as f64))
    .then_ignore(end())
```

The `then_ignore` combinator parses a second pattern after the first, but ignores its output in favour of that of the
first.

The `end` primitive succeeds if it encounters only the end of input.

Combining these together, we now get an error for longer inputs. Unfortunately, this just reveals another problem
(particularly if you're working on a Unix-like platform): any whitespace before or after our digit will upset our
parser and trigger an error.

We can handle whitespace by adding a call to `padded` after our digit parser. This combinator simply ignores any
leading or trailing whitespace around our pattern.

```rust
filter(|c: &char| c.is_ascii_digit())
    .map(|c| Expr::Num(c.to_digit(10).unwrap() as f64))
    .padded_by(filter(|c: &char| c.is_whitespace()))
    .then_ignore(end())
```

This example should have taught you a few important things about Chumsky's parsers:

1. Parsers are lazy: trailing input is ignored

2. Whitespace is not automatically ignored. Chumsky is a general-purpose parsing library, and some languages care very
   much about the structure of whitespace, so Chumsky does too

At this point, things are starting to look a little messy. We've ended up writing 4 lines of code to properly parse a
single digit. Let's clean things up a bit. We'll also make use of a bunch of text-based parser primitives that
come with Chumsky to get rid of some of this cruft.

```rust
let int = text::int(10)
    .map(|s: String| Expr::Num(s.parse().unwrap()))
    .padded();

int.then_ignore(end())
```

That's better. We've also swapped out our custom digit parser with a built-in parser that parses any positive
integer.

## Evaluating simple expressions

We'll now take a diversion away from the parser to create a function that can evaluate our AST. This is the 'heart' of
our interpreter and is the thing that actually performs the computation of programs.

```rust
fn eval(expr: &Expr) -> Result<f64, String> {
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

This function is quite simple: it just recursively calls itself, evaluating each node of the AST until it has a final
result. Any runtime errors simply get thrown back down the stack.

We'll also change our `main` function a little so that we can pass our AST to `eval`.

```rust
fn main() {
    let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();

    match parser().parse(src) {
        Ok(ast) => match eval(ast) {
            Ok(output) => println!("{}", output),
            Err(eval_err) => println!("Evaluation error: {}", eval_err),
        },
        Err(parse_errs) => parse_errs
            .into_iter()
            .for_each(|e| println!("Parse error: {}", e)),
    }
}
```

This looks like a big change, but it's actually quite simple. We're just taking the result of the parse, printing
errors if they occured, or evaluating the AST otherwise. We'll allow for some evaluation operations to produce
runtime errors later.

## Parsing unary operators

Jumping back to our parser, let's handle unary operators. Currently, our only unary operator is `-`, the negation
operator. We're looking to parse any number of `-`, followed by a number. More formally:

```
expr = op* + int
```

We'll also give our `int` parser a new name, 'atom', for reasons that will become clear later.

```rust
let int = text::int(10)
    .map(|s: String| Expr::Num(s.parse().unwrap()))
    .padded();

let atom = int;

let op = |c| just(c).padded();

let unary = op('-')
    .repeated()
    .then(atom)
    .foldr(|_op, rhs| Expr::Neg(Box::new(rhs)));

unary.then_ignore(end())
```

Here, we meet a few new combinators:

- `repeated` will parse a given pattern any number of times (including zero!), collecting the outputs into a `Vec`

- `then` will parse one pattern and then another immediately afterwards, collecting both outputs into a tuple pair

- `foldr` will take an output of the form `(Vec<T>, U)` and will fold it into a single `U` by repeatedly applying
  the given function to each element of the `Vec<T>`

This last combinator is worth a little more consideration. We're trying to parse *any number* of negation operators,
followed by a single atom (for now, just a number). This might give us an output like this:

```rust
(['-', '-', '-'], Num(42.0))
```

The `foldr` function repeatedly applies the function to 'fold' the elements into a single element, like so:

```
['-',   '-',   '-'],   Num(42.0)
  |      |      |          |
  |      |       \        /
  |      |     Neg(Num(42.0))
  |      |         |
  |       \       /
  |  Neg(Neg(Num(42.0)))
  |          |
   \        /
Neg(Neg(Neg(Num(42.0))))
```

This may be a little hard to conceptualise for those used to imperative programming, but for functional programmers
it should come naturally: `foldr` is just equivalent to `reduce`!

Give the interpreter a try. You'll be able to enter inputs as before, but also values like `-17`. You can even apply
the negation operator multiple times: `--9` will yield a value of `9` in the command line.

This is exciting: we've finally started to see our interpreter perform useful (sort of) computations!

## Parsing binary operators

Let's keep the momentum going and move over to binary operators. Traditionally, these pose quite a problem for
parsers. To parse an expression like `3 + 4 * 2`, it's necessary to understand that multiplication
[binds more eagerly than addition](https://en.wikipedia.org/wiki/Order_of_operations) and hence is applied first.
Therefore, the result of this expression is `11` and not `14`.

Parsers employ a range of strategies to handle these cases, but for Chumsky things are simply: the most eagerly binding
(highest 'precedence') operators should be those that get considered first when parsing.

It's worth noting that summation operators (`+` and `-`) are typically considered to have the *same* precedence as
one-another. The same also applies to product operators (`*` and `/`). For this reason, we each group as a single
pattern.

At each stage, we're looking for a simple pattern: a unary value, following by any number of a combination of an
operator and a unary value. More formally:

```
expr = unary + (op + unary)*
```

Let's expand our parser.

```rust
let int = text::int(10)
    .map(|s: String| Expr::Num(s.parse().unwrap()))
    .padded();

let atom = int;

let op = |c| just(c).padded();

let unary = op('-')
    .repeated()
    .then(atom)
    .foldr(|_op, rhs| Expr::Neg(Box::new(rhs)));

let product = unary.clone()
    .then(op('*').to(Expr::Mul as fn(_, _) -> _)
        .or(op('/').to(Expr::Div as fn(_, _) -> _))
        .then(unary)
        .repeated())
    .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)));

let sum = product.clone()
    .then(op('+').to(Expr::Add as fn(_, _) -> _)
        .or(op('-').to(Expr::Sub as fn(_, _) -> _))
        .then(product)
        .repeated())
    .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)));

sum.then_ignore(end())
```

Another three combinators are introduced here:

- `or` attempts to parse a pattern and, if unsuccessful, instead attempts another pattern

- `to` is similar to `map`, but instead of mapping the output, entirely overrides the output with a new value. In our
  case, we use it to convert each binary operator to a function that produces the relevant AST node for that operator.

- `foldl` is very similar to `foldr` in the last section but, instead of operating on a `(Vec<_>, _)`, it operates
  upon a `(_, Vec<_>)`, going backwards to combine values together with the function

Give the interpreter a try. You should find that the interpreter can correctly handle both unary and binary operations
combined in arbitrary configurations, correctly handling precedence. You can use it as a calculator!

## Parsing parentheses

A new challenger approaches: *nested expressions*. Sometimes, we want to override the default operator precedence rules
entirely. We can do this by nesting expressions within parentheses, like `(3 + 4) * 2`. How do we handle this?

The creation of the `atom` pattern a few sections before was no accident: parentheses have a greater precedence than
any operator, so we should treat a parenthesised expression as if it were equivalent to a single value. We call things
that behave like single values 'atoms' by convention.

We're going to hoist our entire parser up into a closure, allowing us to define it in terms of itself.

```rust
recursive(|expr| {
    let int = text::int(10)
        .map(|s: String| Expr::Num(s.parse().unwrap()))
        .padded();

    let atom = int
        .or(expr.delimited_by('(', ')'));

    let op = |c| just(c).padded();

    let unary = op('-')
        .repeated()
        .then(atom)
        .foldr(|_op, rhs| Expr::Neg(Box::new(rhs)));

    let product = unary.clone()
        .then(op('*').to(Expr::Mul as fn(_, _) -> _)
            .or(op('/').to(Expr::Div as fn(_, _) -> _))
            .then(unary)
            .repeated())
        .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)));

    let sum = product.clone()
        .then(op('+').to(Expr::Add as fn(_, _) -> _)
            .or(op('-').to(Expr::Sub as fn(_, _) -> _))
            .then(product)
            .repeated())
        .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)));

    sum.padded()
})
    .then_ignore(end())
```

There are a few things worth paying attention to here.

1. `recursive` allows us to define a parser recursively in terms of itself by giving us a copy of it within the
   closure's scope

2. We use the recursive definition of `expr` within the definition of `atom`. We use the new `delimited_by` combinator
   to allow it to sit nested within a pair of parentheses

3. The `then_ignore(end())` call has *not* been hoisted inside the `recursive` call. This is because we only want to
   parse an end of input on the outermost expression, not at every level of nesting

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

```
let <ident> = <expr>; <expr>
```

We only want `let`s to appear at the outermost level of the expression, so we leave it out of the original recursive
expression definition. However, we also want to be able to chain `let`s together, so we put them in their own recursive
definition. We call it `decl` ('declaration') because we're eventually going to be adding `fn` syntax too.

```rust
let ident = text::ident()
    .padded();

let expr = recursive(|expr| {
    let int = text::int(10)
        .map(|s: String| Expr::Num(s.parse().unwrap()))
        .padded();

    let atom = int
        .or(expr.delimited_by('(', ')'))
        .or(ident.map(Expr::Var));

    let op = |c| just(c).padded();

    let unary = op('-')
        .repeated()
        .then(atom)
        .foldr(|_op, rhs| Expr::Neg(Box::new(rhs)));

    let product = unary.clone()
        .then(op('*').to(Expr::Mul as fn(_, _) -> _)
            .or(op('/').to(Expr::Div as fn(_, _) -> _))
            .then(unary)
            .repeated())
        .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)));

    let sum = product.clone()
        .then(op('+').to(Expr::Add as fn(_, _) -> _)
            .or(op('-').to(Expr::Sub as fn(_, _) -> _))
            .then(product)
            .repeated())
        .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)));

    sum.padded()
});

let decl = recursive(|decl| {
    let r#let = just("let")
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
    .then_ignore(end())
```

There's nothing in the definition of `r#let` that you haven't seen before: familiar combinators, but combined in
different ways. It selectively ignores parts of the syntax that we don't care about after validating that it exists,
then uses those elements that it does care about to create an `Expr::Let` AST node.

Another thing to note is that the definition of `ident` will parse `"let"`. To avoid the parser accidentally deciding
that `"let"` is a variable, we place `r#let` earlier in the or chain than `expr` so that it prioritises the correct
interpretation. As mentioned in previous sections, Chumsky handles ambiguity simply by choosing the first successful
parse it encounters, so making sure that we declare things in the right order can sometimes be important.

You should now be able to run the interpreter and have it accept an input such as

```
let five = 5;
five * 3
```

Unfortunately, the `eval` function will panic because we've not yet handled `Expr::Var` or `Expr::Let`. Let's do that
now.

```rust
fn eval<'a>(expr: &'a Expr, vars: &mut Vec<(&'a String, f64)>) -> Result<f64, String> {
    match expr {
        Expr::Num(x) => Ok(*x),
        Expr::Var(name) => if let Some((_, val)) = vars.iter().rev().find(|(var, _)| *var == name) {
            Ok(*val)
        } else {
            Err(format!("Cannot find variable `{}` in scope", name))
        },
        Expr::Neg(a) => Ok(-eval(a, vars)?),
        Expr::Add(a, b) => Ok(eval(a, vars)? + eval(b, vars)?),
        Expr::Sub(a, b) => Ok(eval(a, vars)? - eval(b, vars)?),
        Expr::Mul(a, b) => Ok(eval(a, vars)? * eval(b, vars)?),
        Expr::Div(a, b) => Ok(eval(a, vars)? / eval(b, vars)?),
        Expr::Let { name, rhs, then } => {
            let rhs = eval(rhs, vars)?;
            vars.push((name, rhs));
            let output = eval(then, vars);
            vars.pop();
            output
        },
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
   declared variable with the same name) to find the variables's value. If we can't find a variable of that name, we
   generate a runtime error which gets propagated back up the stack.

Make sure to test the interpreter. Try experimenting with `let` declarations to make sure things aren't broken. In
particular, it's worth testing variable shadowing by ensuring that the following program produces `8`:

```
let x = 5;
let x = 3 + x;
x
```

## Parsing functions

*TODO*

## Extension tasks

- Split token lexing into a separate compilation stage to avoid the need for `.padded()` in the parser

- Add more operators

- Add an `if <expr> then <expr> else <expr>` ternary operator

- Add values of different types by turning `f64` into an `enum`.

- Format the error message in a more useful way, perhaps by providing a reference to the original code
