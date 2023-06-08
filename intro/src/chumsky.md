# Chumsky

Chumsky is a parser combinator library designed by humans, for humans.

The library consists of many smaller parsers, which are designed to be combined
together to create a parser for a larger unit. For example, you can use the
smaller combinators to parse a programming language like [Tao](https://github.com/zesterer/tao).

## Design

Chumsky is designed such that it should be:

* easy to use
* modular and extensible
* fast enough while allowing for quality errors
* type driven, pushing users away from anti-patterns at compile-time
* a mature and "batteries included" solution for context-free parsing

## Performance

As pointed out in the last design point, Chumsky makes a focus to provide
high-quality errors and easy-of-use over performance. This being said, Chumsky
should be able to hold its own when compared to the rest of your program. Due to
the nature of parsing, it is _extremely_ difficult to create a sensible benchmark 
of a parser, as it depends largely on what is being parsed. That said, benchmarks are
available on [GitHub](https://github.com/zesterer/chumsky/blob/main/benches/). 
Here is the current benchmark between this library and another parser combinator
library, [`pom`](https://github.com/J-F-Liu/pom):

```
test chumsky ... bench:   4,782,390 ns/iter (+/- 997,208)
test pom     ... bench:  12,793,490 ns/iter (+/- 1,954,583)
```

This is obviously slower than a handwritten parser, but that's okay. Chumsky's
goal is not to be the fastest, and if you're far enough in development that
parsing performance is the actual problem, it's likely time to be moving to a
hand-written parser anyway.
