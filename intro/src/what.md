# Intro to Parsing Combinators

Parser combinators are a technique for implementing parsers by defining them in
terms of other, typically smaller, parsers. A short example would be defining
parsing a decimal number like `3.14159` as a sequence of digits, a dot, and then
a final sequence of digits.

The result of such a definiton is a [recursive descent parser](https://en.wikipedia.org/wiki/Recursive_descent_parser),
which transforms a stream of tokens into some output. Using parser combinators
to define parsers is roughly analogous to using Rust's [`Iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html)
trait to define iterative algorithms: the type-driven API of `Iterator` makes it
more difficult to make mistakes and easier to encode complicated iteration logic
than if one were to write the same code by hand. The same is true of parser
combinators.
