# Parsing Numbers

Chumsky is a 'parser combinator' library. It allows the creation of parsers by combining together many smaller
parsers. The very smallest parsers are called 'primitives' and live in the
[`primitive`](https://docs.rs/chumsky/latest/chumsky/primitive/index.html) module.

We're going to want to start by parsing the simplest element of Foo's syntax: numbers.

## Parsing Digit
<hr>

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

## Parsing Digit*s*
<hr>

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

We can handle whitespace by adding a call to `padded_by` (which ignores a given pattern before and after the first)
after our digit parser, and a repeating filter for any whitespace characters.

```rust
filter(|c: &char| c.is_ascii_digit())
    .map(|c| Expr::Num(c.to_digit(10).unwrap() as f64))
    .padded_by(filter(|c: &char| c.is_whitespace()).repeated())
    .then_ignore(end())
```

This example should have taught you a few important things about Chumsky's parsers:

1. Parsers are lazy: trailing input is ignored

2. Whitespace is not automatically ignored. Chumsky is a general-purpose parsing library, and some languages care very
   much about the structure of whitespace, so Chumsky does too

## Cleanup and Shortcuts
<hr>

At this point, things are starting to look a little messy. We've ended up writing 4 lines of code to properly parse a
single digit. Let's clean things up a bit. We'll also make use of a bunch of text-based parser primitives that
come with Chumsky to get rid of some of this cruft.

```rust
let int = text::int(10)
    .map(|s: String| Expr::Num(s.parse().unwrap()))
    .padded();

int.then_ignore(end())
```

That's better. We've also swapped out our custom digit parser with a built-in parser that parses any non-negative
integer.

