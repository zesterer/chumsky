# Chumsky: A Tutorial

*Please note that this tutorial is kept up to date with the `master` branch and
not the most stable release: small details may differ!*

In this tutorial, we'll develop a parser (and interpreter!) for a programming
language called 'Foo'.

Foo is a small language, but it's enough for us to have some fun. It is very
simple, but it is complex enough to allow us to get to grips with parsing using
Chumsky, containing many of the elements you'd find in a 'real' programming
language.

Here's some sample code written in Foo:

```
let seven = 7;
fn add x y = x + y;
add(2, 3) * -seven
```

You can find the source code for the full interpreter in `examples/foo.rs` in
the main repository.

## Setting up

Create a new binary project (`cargo new --bin foo`), add the latest version of
Chumsky as a dependency (`cargo add chumsky`), and place the following in your
`main.rs`:

```rust
use chumsky::prelude::*;

const SRC: &str = "";

fn main() {
    println!("{:?}", parser().parse(SRC));
}

/// A Foo expression.
#[derive(Debug)]
enum Expr {}

fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    todo()
}
```

So `main` will just parse our `SRC` constant and print what happened.

If this were a "proper" program we'd probably read in a filename of what to
parser from a command line argument or something, but this is a parsing
tutorial, so we'll just use a string literal. Also, it makes the example code
easy to put into the tutorial that way.

If we actually try to run the program right now then it'll crash like this:
```
D:\dev\chumsky-tutorial>cargo run
   Compiling chumsky-tutorial v0.1.0 (D:\dev\chumsky-tutorial)
    Finished dev [unoptimized + debuginfo] target(s) in 1.11s
     Running `target\debug\main.exe`
thread 'main' panicked at 'not yet implemented: Attempted to use an unimplemented parser.'
```

As we develop our program we will fill in the `parser` function with more and
more complex parsers that will be able to handle more and more Foo code.

## Parser Combinators

Chumsky is a "parser combinator" library. Parser combinator design is about
starting with the smallest possible parsers, "primitives", and combinging them
into ever bigger parsers.

With the `chumsky` library the primitive parsers live in the
[`primitive`][crate-primitive] module. When you're developeing a parser from
nothing, start by looking there.

[crate-primitive]: https://docs.rs/chumsky/latest/chumsky/primitive/index.html

Right now our entire parser is `todo`, so we've got a lot to build.

## The `Parser` Trait

If we were to check out the [`Parser`] trait we'd see something like this:

[crate-Parser]: https://docs.rs/chumsky/latest/chumsky/trait.Parser.html

```rust
pub trait Parser<I: Clone, O> {
    type Error: Error<I>;
  // [+] Show 34 methods
}
```

There's three things to pay attention to:
* `I` is the input. We'll have a stream of inputs tokens, meaning 0 or more. In
  our case with Foo, we'll be parsing the individual `char` values of the source
  string.
* `O` is the output. Similar to a normal Rust function, there's *just one*
  output for the whole parser. As we combine parsers they'll also combine their
  output. So no matter how many parsers we combine, at any level of the parsing
  process there's just one output. Keep in mind that "just one output" could be
  "just one Vec", or a struct of all the things you've parsed together, or
  anything else.
* The `Error` associated type is something that implements chumsky's
  [`Error`][crate-error-Error] trait. Any time you're parsing the parse might go
  wrong, and when it does you get an error.

[crate-error-Error]: https://docs.rs/chumsky/latest/chumsky/error/trait.Error.html

There's also those 34 methods, but those are all different defaulted ways to do
parsing things. It's kinda like with [`Iterator`][core-iter-Iterator], where
there's piles of default methods you don't need to learn all at once. We're not
going to look at any of that right now.

[core-iter-Iterator]: https://doc.rust-lang.org/nightly/core/iter/trait.Iterator.html

## Put Another Way: Parser Combinators Are Like Functions That Return Results

When you get down to it, this is all we're making:

```rust
fn the_parser(stream: impl Iterator<Item=Token>) -> Result<Success, ErrInfo<Token>>;
```

If you can understand taking in an iterator and then either building a success
value or returning the iterator's value caused a parse error (along with maybe
some context info), then you already have all the background you need for
working with parser combinators.

Why do we need an entire library for building such a simple thing? Because
`rustc` is a smol bean that needs all the steps explained very clearly, one at a
time. And the library helps us do that.

## Parser Primitive: `todo`

Alright, back to the example code.

Right now our `parser` function just calls `todo()`. This makes a `Todo` value,
which implements `Parser` for all possible inputs and outputs. Handy. It does
this by just panicing as soon as you ask it to parse anything. Less handy.

This is actually useful, as evidenced by the fact that we've already used it. I
know you're thinking "Just put `todo!()` in there!", but you can't. For kinda
dumb technical reasons we don't need to go into, if a function returns any kind
of `impl Parser` then you can't use `todo!()` or `unimplemented!()` or any other
thing that panics or returns `!`. It just gets you a nasty type error. Try it if
you want.

Just remember this part: if you *would* want to use the `todo!()` macro in your
code, just use the `todo` parser primitive instead.

The fact that we call the `todo` function to build a `Todo` value, rather than
calling `Todo::new` like most of Rust uses, that's just a style thing. All of
chumsky's primitive parsers work like this, it's fine.

## Parser Primitive: `filter`

Let's actually parse instead of panic. Except remember that we *start small* and
then *build up*. To start we won't parse even one line of our sample program.
Instead, we'll parse just a single digit.

Enter the [`filter`][crate-primitive-filter] primitive.

It works kinda like the filter iterator method. You pass a closure that accepts
an input value and then determines if the value is allowed or not. By "allowed"
we mean "allowed at this point in the parse". Think of it like this: you *can*
type integers into a Rust source file, but you *can't* type integers as the name
of a function. They're not allowed in that position.

Unlike with an iterator's filter method, if the value passed to a filter parser
is not allowed the parsing will *error* instead of moving on. That might sound
bad to error so easily, but we'll have ways to handle that soon enough so don't
worry about that error too much.

[crate-primitive-filter]: https://docs.rs/chumsky/latest/chumsky/primitive/fn.filter.html

Armed with `filter`, we can *almost* parse a single digit.

The `filter` primitive returns its input as the output, so with `filter` alone
the output is a `char` value. We want to fit it into our `Expr` enum, so we'll
add a `Num(f64)` variant. Now that `Expr` allows us to have a number, we have to
change the output of `filter` to give us a number.

Now let's think. If we had an *actual* function that returned a `Result<T, E>`,
but `T` was wrong for what we wanted, what would we do? Of course we'd call
`map`. Chumsky has us set, and one of those 34 methods we skipped earlier is a
[`map`][Parser-map] method that does just what you think it should:

[Parser-map]: https://docs.rs/chumsky/latest/chumsky/trait.Parser.html#method.map

```rust
use chumsky::prelude::*;

const SRC: &str = "7";

fn main() {
    println!("{:?}", parser().parse(SRC));
}

/// A Foo expression.
#[derive(Debug)]
enum Expr {
    Num(f64),
}

fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    filter(|c: &char| c.is_ascii_digit())
        .map(|c: char| Expr::Num(c.to_digit(10).unwrap() as f64))
}
```

And let's give that a run to see what happens:

```
D:\dev\chumsky-tutorial>cargo run
   Compiling chumsky-tutorial v0.1.0 (D:\dev\chumsky-tutorial)
    Finished dev [unoptimized + debuginfo] target(s) in 0.03s
     Running `target\debug\main.exe`
Ok(Num(7.0))
```

Phenomenal. Cosmic. Power.

## Parser Primitive: `end`

Okay, so we can parse the number 7. Let's try parsing a bigger number, like 75.

```rust
const SRC: &str = "75";
```

```
D:\dev\chumsky-tutorial>cargo run
   Compiling chumsky-tutorial v0.1.0 (D:\dev\chumsky-tutorial)
    Finished dev [unoptimized + debuginfo] target(s) in 1.42s
     Running `target\debug\main.exe`
Ok(Num(7.0))
```

Oops. Maybe... not as much cosmic power as we thought.

See, these parser combinators are "lazy". They'll do the least amount of work
they can to get a result. Just like most programmers. Again, and I know I keep
saying this, but we can make another comparison with Rust's iterators. If you
don't force the iterator to evaluate all the steps, it'll just stop early. If
you don't force the parser to get all the way to the end of the input, it'll
just stop early too.

We can use another default `Parser` function here:
[`then_ignore`][Parser-then_ignore]

[Parser-then_ignore]: https://docs.rs/chumsky/latest/chumsky/trait.Parser.html#method.then_ignore

A "then_ignore" parse will parser the first thing (right now that's a digit) and
then it will run the parser you pass and *ignore* whatever comes out. So, we
could parse a digit and "then ignore" some second parser (like for comments
maybe). The trick is, the ignoring only happens *on success*. If the then_ignore
parser fails with an error then our entire combinated parse will fail with that
error.

This brings us to the [`end`][crate-primitive-end] primitive. All it does is
parse the end of the input stream. If the input stream isn't done when the `end`
parser runs then it will error.

[crate-primitive-end]: https://docs.rs/chumsky/latest/chumsky/primitive/fn.end.html

So we'll filter for a digit, and then ignore the end of input. Let's check if
that works for just the 7.

```rust
const SRC: &str = "7";

fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    filter(|c: &char| c.is_ascii_digit())
        .map(|c: char| Expr::Num(c.to_digit(10).unwrap() as f64))
        .then_ignore(end())
}
```

```
Ok(Num(7.0))
```

And then if it's 75?

```rust
const SRC: &str = "75";
```
```
Err([Simple { span: 1..2, reason: Unexpected, expected: {None}, found: Some('5'), label: None }])
```

Well, we got an error, but that's what we were after, kinda. What we definitely
*did not* want to have happen is for the source string to be more than just 7
and only get 7 our as our parse. Now the source string is 75 and we're getting
an error that it's not the end of the input. That's progress, of a kind.

To read a number we need to read a digit *and then another digit*. Possibly even
a third digit, or more! Golly, this could get complicated. But with the help of
another `Parser` method, [`repeated`][Parser-repeated], we can do repeated digit
parsing to form a number.

[Parser-repeated]: https://docs.rs/chumsky/latest/chumsky/trait.Parser.html#method.repeated

```rust
fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    filter(|c: &char| c.is_ascii_digit())
        .map(|c: char| Expr::Num(c.to_digit(10).unwrap() as f64))
        .repeated()
        .then_ignore(end())
}
```
```
error[E0271]: type mismatch resolving `<fn((Vec<Expr>, ())) -> Vec<Expr> as FnOnce<((Vec<Expr>, ()),)>>::Output == Expr`
  --> src\bin\main.rs:15:16
   |
15 | fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
   |                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected struct `Vec`, found enum `Expr`
   |
   = note: expected struct `Vec<Expr>`
                found enum `Expr`
   = note: required because of the requirements on the impl of `chumsky::Parser<char, Expr>` for `chumsky::combinator::Map<Then<Repeated<chumsky::combinator::Map<chumsky::primitive::Filter<[closure@src\bin\main.rs:16:12: 16:22], chumsky::error::Simple<char>>, [closure@src\bin\main.rs:17:14: 17:23], char>>, chumsky::primitive::End<chumsky::error::Simple<char>>>, fn((Vec<Expr>, ())) -> Vec<Expr>, (Vec<Expr>, ())>`
```

Oops.

Oh, right, of course, we don't repeat the expression output, we repeat the digit filtering.

```rust
fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    filter(|c: &char| c.is_ascii_digit())
        .repeated()
        .map(|c: char| Expr::Num(c.to_digit(10).unwrap() as f64))
        .then_ignore(end())
}
```
```
error[E0631]: type mismatch in closure arguments
   --> src\bin\main.rs:18:10
    |
18  |         .map(|c: char| Expr::Num(c.to_digit(10).unwrap() as f64))
    |          ^^^ --------- found signature defined here
    |          |
    |          expected due to this
    |
    = note: expected closure signature `fn(Vec<char>) -> _`
               found closure signature `fn(char) -> _`
```

Okay that seems closer to what we need. Once we have repeated digits we don't
have just one `char` we have a whole `Vec<char>`. We just apply a little dancing
around with that vector and we can get an `f64` out of it. Then that can be our
`Expr::Num`.

```rust
fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    filter(|c: &char| c.is_ascii_digit())
        .repeated()
        .map(|digits: Vec<char>| {
            Expr::Num(
                digits
                    .into_iter()
                    .map(|c| c.to_digit(10).unwrap() as f64)
                    .fold(0.0, |old, new| old * 10.0 + new),
            )
        })
        .then_ignore(end())
}
```
```
Ok(Num(75.0))
```

That code is... pretty ugly. I'll admit.

But it *does* parse the number 75 like we want.

What happens if we put some whitespace around the number? We gotta let people
have their whitespace.

```rust
const SRC: &str = " 75";
```
```
Err([Simple { span: 0..1, reason: Unexpected, expected: {None}, found: Some(' '), label: None }])
```

Aw dag. More errors.

This time it calls for the [`padded_by`][Parser-padded_by] method. This takes a
parser which *might* occur on either side of the inner parser, and the final
output is the inner parser's output. If the padding is *not* present then things
will continue just fine, without error.

[Parser-padded_by]: https://docs.rs/chumsky/latest/chumsky/trait.Parser.html#method.padded_by

Of course, let's not forget that whitespace can also be repeated too.
```rust
const SRC: &str = "    75";

fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    filter(|c: &char| c.is_ascii_digit())
        .repeated()
        .map(|digits: Vec<char>| {
            Expr::Num(
                digits
                    .into_iter()
                    .map(|c| c.to_digit(10).unwrap() as f64)
                    .fold(0.0, |old, new| old * 10.0 + new),
            )
        })
        .padded_by(filter(|c: &char| c.is_whitespace()).repeated())
        .then_ignore(end())
}
```
```
Ok(Num(75.0))
```

## Pre-Combined Parsers

Okay, so, uh, maybe putting the entire parser built out of primitive actions into a single function is... less than the best idea.

Let's try the [`int`][crate-text-int] function. It takes a radix and then
returns a bunch of characters that match the radix. What's neat is that this
isn't just a `Parser`, it's a [`TextParser`]! That's like a normal `Parser`, but
more! In this case, the more is that we get the [`padded`][TextParser-padded]
method, which cuts repeated whitespace before and after the parse.

[crate-text-int]: https://docs.rs/chumsky/latest/chumsky/text/fn.int.html
[crate-text-TextParser]: https://docs.rs/chumsky/latest/chumsky/text/trait.TextParser.html
[TextParser-padded]: https://docs.rs/chumsky/latest/chumsky/text/trait.TextParser.html#method.padded

```rust
fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    let int =
        text::int(10).map(|s: String| Expr::Num(s.parse().unwrap())).padded();
    int.then_ignore(end())
}
```
```
Ok(Num(75.0))
```
