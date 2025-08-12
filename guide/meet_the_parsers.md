# Meet The Parsers

Chumsky provides a whole suite of parser components, both primitives and combinators. This page lists the ones you'll
most commonly use. They're roughly ranked in order of importance, with the most commonly used at the top of each list.

As a reminder: primitives are the most basic building blocks of a parser, while combinators allow you to combine them
together into parsers that can handle increasingly complex grammars.

Note that when the term *'recognises'* is used, it means that all other inputs are rejected by the parser, resulting in
backtracing or an error.

Each parser has inline documentation, including longer and more useful examples.

- [Primitives](#primitives)

- [Combinators](#combinators)

    - [Combining parsers](#combining-parsers)

    - [Generating and manipulating outputs](#generating-and-manipulating-outputs)

    - [Handling and emitting errors](#handling-and-emitting-errors)

    - [Text-oriented parsing](#text-oriented-parsing)

    - [Utility and error recovery](#utility-and-error-recovery)

    - [Backtracking and input manipulation](#backtracking-and-input-manipulation)

    - [Context-sensitive parsing](#context-sensitive-parsing)

## Primitives

Primitives are the most basic building blocks of a parser and typically perform a very simple action such as recognising
a particular token or set of tokens.

| Name        | Examples                            | Description                                                                                                             |
|-------------|-------------------------------------|-------------------------------------------------------------------------------------------------------------------------|
| [`just`]    | `just('a')`, `just("hello")`        | Recognises a specific token or an exact ordered sequence of tokens (see [`Seq`] and [`OrderedSeq`]).                    |
| [`none_of`] | `none_of(';')`, `none_of("xyz")`    | Recognises any single token that is *not* part of a given sequence of tokens (see [`Seq`]).                             |
| [`one_of`]  | `one_of('0'..='9')`, `one_of("<>")` | Recognises any single token that *is* part of a given sequence of tokens (see [`Seq`]).                                 |
| [`any`]     | `any().filter(char::is_whitespace)` | Recognises any single token, but not the end of the input.                                                              |
| [`todo()`]  | `foo.then(todo())`                  | A placeholder parser that panics when invoked. Spiritually similar to the [`todo!`] macro.                              |
| [`custom`]  | (see documentation for examples)    | Allows implementing custom parsing logic, see the documentation for more information about how to write custom parsers. |
| [`end`]     | `x.then(end())`                     | Recognises only the end of the input. Not to be confused with [`empty`].                                                |
| [`empty()`] | `empty().then(y)`                   | Recognises no input (i.e: it will always succeed, without advancing the input). Not to be confused with [`end`].        |

## Combinators

Combinators allow parsers to be combined together to make larger parsers. You can think of them as 'parser operators'.

Because there are rather a lot of combinators, this section is split into categories to make finding the combinator
you're looking for easier.

### Combining parsers

Combinators that allow combining smaller parsers together to make parsers for more complex grammars.

| Name                            | Example                               | Description                                                                                                                                                                             |
|---------------------------------|---------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [`Parser::then`]                | `a.then(b)`                           | Parse one pattern and then another, producing a tuple of the two parsers outputs as an output.                                                                                          |
| [`Parser::or`]                  | `a.or(b)`                             | Parse one pattern, or another if the first failed to parse. This allows you to implement branching parser logic that recognises one of many different patterns.                         |
| [`Parser::ignore_then`]         | `a.ignore_then(b)`                    | Parse one pattern and then another, producing only the output of the second as an output (i.e: ignoring the output of the first).                                                       |
| [`Parser::then_ignore`]         | `a.then_ignore(b)`                    | Parse one pattern and then another, producing only the output of the first as an output (i.e: ignoring the output of the second).                                                       |
| [`Parser::delimited_by`]        | `a.delimited_by(x, y)`                | Parses a pattern, delimited by two other patterns on either side. Most often used to parse parenthesiesed expressions, blocks, or arrays.                                               |
| [`Parser::padded_by`]           | `a.padded_by(b)`                      | Parses a pattern, delimited by a pattern on either side. Often used to consume whitespace or other irrelevant input that surrounds a pattern.                                           |
| [`Parser::repeated`]            | `a.repeated().collect::<Vec<_>>()`    | Parse the given pattern any number of times (including none at all!). Note that [`Repeated`] implements the [`IterParser`] trait, so can be used with [`IterParser::collect`].          |
| [`Parser::separated_by`]        | `a.separated_by(b).count()`           | Parses a pattern many times, interspersed with another pattern. Commonly used to parse things like comma-separated lists. Like [`Repeated`], [`SeparatedBy`] implements [`IterParser`]. |
| [`Parser::or_not`]              | `a.or_not()`                          | Attempt to parse a pattern, always succeeding with either `Some(...)` or `None` depending on whether parsing was successful. Can be used to optionally parse patterns.                  |
| [`Parser::foldl`]               | `a.foldl(b.repeated(), ...)`          | Parses a pattern, and then folds an [`IterParser`] into its output using the given function. Often used to parse binary operators.                                                      |
| [`IterParser::foldr`]           | `a.repeated().foldr(b, ...)`          | Parses elements of an [`IterParser`], then a second pattern, folding the elements into the second parser's output. Often used to parse unary operators.                                 |

### Generating and manipulating outputs

Combinators that manipulate, generate, or combine the output of parsers in some manner (see
[backtracking and input manipulation](#backtracking-and-input-manipulation) for combinators that recover from errors).

| Name                            | Example                               | Description                                                                                                                                                                             |
|---------------------------------|---------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [`Parser::map`]                 | `a.map(...)`                          | Map the output of a parser using the given mapping function.                                                                                                                            |
| [`Parser::map_with`]            | `a.map_with(...)`                     | Map the output of a parser using the given mapping function, with access to metadata associated with the output.                                                                        |
| [`Parser::to_slice`]            | `a.to_slice()`                        | Parse a pattern. Discard the output of the pattern and instead use a slice of the input that the pattern corresponds to as the output. Requires inputs that implement [`SliceInput`].   |
| [`Parser::to`]                  | `a.to(x)`                             | Parse a pattern, ignoring the output value and using a constant value as the output value instead.                                                                                      |
| [`Parser::ignored`]             | `a.ignored()`                         | Parse a pattern, ignoring the output value and using `()` as the output value instead.                                                                                                  |
| [`IterParser::collect`]         | `a.repeated().collect::<Vec<_>>()`    | Collects elements of an [`IterParser`] into a type implementing [`Container`].                                                                                                          |
| [`IterParser::collect_exactly`] | `a.repeated().collect::<Vec<_>>()`    | Collects elements of an [`IterParser`] into an exact-sized type implementing [`ContainerExactly`].                                                                                      |
| [`IterParser::count`]           | `a.repeated().count()`                | Count the number of elements produced by an [`IterParser`].                                                                                                                             |
| [`Parser::unwrapped`]           | `a.unwrapped()`                       | Parse a pattern that returns either a [`Result`] or an [`Option`], then unwrap them.                                                                                                    |

### Handling and emitting errors

Combinators that manipulate or emit errors, along with fallibly validating parser outputs.

| Name                            | Example                               | Description                                                                                                                                                                             |
|---------------------------------|---------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [`Parser::map_err`]             | `a.map_err(...)`                      | Parse a pattern. On failure, map the parser error to another value. Often used to customise error messages or add extra information to them.                                            |
| [`Parser::map_err_with_state`]  | `a.lazy()`                            | Like [`Parser::map_err`], but provides access to the parser state (see [`Parser::parse_with_state`] for more information).                                                              |
| [`Parser::try_foldl`]           | `a.try_foldl(...)`                    | Left-fold the output of the parser into a single value, possibly failing during the reduction. If the function produces an error, the parser fails with that error.                                              |
| [`Parser::try_map`]             | `a.try_map(...)`                      | Map the output of a parser using the given fallible mapping function. If the function produces an error, the parser fails with that error.                                              |
| [`Parser::try_map_with`]        | `a.try_map_with(...)`           |     | Map the output of a parser using the given fallible mapping function, with access to output metadata. If the function produces an error, the parser fails with that error.              |
| [`Parser::validate`]            | `a.validate(...)`                     | Parse a pattern. On success, map the output to another value with the opportunity to emit extra secondary errors. Commonly used to check the validity of patterns in the parser.        |
| [`Parser::filter`]              | `any().filter(char::is_lowercase)`    | Parse a pattern and apply the given filtering function to the output. If the filter function returns [`false`], the parser fails.                                                       |
| [`Parser::labelled`]            | `a.labelled("a")`                     | Parse a pattern, labelling it. What exactly this does depends on the error type, but it is generally used to give a pattern a more general name (for example, "expression").            |

### Text-oriented parsing

Combinators intended only for the parsing and manipulation of text-like inputs.

| Name                            | Example                               | Description                                                                                                                                                                             |
|---------------------------------|---------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [`Parser::padded`]              | `a.padded()`                          | Skips whitespace on either side of a pattern for text-like inputs specifically (i.e: those with [`u8`] or [`char`] tokens). A more specialised version of [`Parser::padded_by`].        |
| [`Parser::from_str`]            | `just("true").from_str().unwrapped()` | Parse a pattern that outputs a string, then use Rust's [`FromStr`] trait to parse it. Often paired with [`Parser::unwrapped`] to unwrap any errors.                                     |

### Utility and error recovery

Miscellaneous combinators and those that relate to error recovery.

| Name                            | Example                               | Description                                                                                                                                                                             |
|---------------------------------|---------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [`Parser::boxed`]               | `a.boxed()`                           | Performs type-erasure on a parser, allocating it on the heap. Stategically boxing of parsers can improve compilation times and allows dynamically building up parsers at runtime.       |
| [`Parser::recover_with`]        | `a.recover_with(r)`                   | Attempt to parse a pattern. On failure, the given recovery strategy is used to attempt to recovery from the error. See the documentation for more information.                          |
| [`Parser::memoized`]            | `a.memoized()`                        | Parse a pattern, but remember whether it succeeded or failed and reuse that information when parsing the same input again. Allows expressing left-recursive or exponential patterns.    |

### Backtracking and input manipulation

Combinators that perform internal backtracking or that manipulate inputs in order to function.

| Name                            | Example                               | Description                                                                                                                                                                             |
|---------------------------------|---------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [`Parser::not`]                 | `a.and_is(b.not())`                   | Doesn't parse anything, but rejects anything that *would* parse as the given pattern. On success, no input is consumed.                                                                 |
| [`Parser::and_is`]              | `a.and_is(b)`                         | Parses one pattern, but only if the other parser also parses at the same location.                                                                                                      |
| [`Parser::rewind`]              | `a.then(b.rewind())`                  | Parses a pattern. On success, rewinds the input to the start of the pattern as if it had never been parsed. Often used parse patterns that expect to have something else after them     |
| [`Parser::lazy`]                | `a.lazy()`                            | Only useful on 'top-level' parsers. Makes the parser lazy such that it will only recognise as much input as it can and no more.                                                         |
| [`Parser::nested_in`]           | `a.nested_in(b)`                      | Parse one pattern from the output of another pattern, using the output of the second parser as the input of the first. Often used to pass token trees.                                  |

### Context-sensitive parsing

Combinators that allow the parsing of context-sensitive grammars (usually beyond the capability of top-down parsers).

| Name                            | Example                               | Description                                                                                                                                                                             |
|---------------------------------|---------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [`Parser::ignore_with_ctx`]     | `a.ignore_with_ctx(b)`                | Parse one pattern and use its output as context for another pattern, doesn't return the context. See [`ConfigParser::configure`] for information about context-sensitive parsing.       |
| [`Parser::then_with_ctx`]       | `a.then_with_ctx(b)`                  | Parse one pattern and use its output as context for another pattern. returns the context. See [`ConfigParser::configure`] for information about context-sensitive parsing.              |
| [`Parser::with_ctx`]            | `a.with_ctx(ctx)`                     | Parse a pattern with the provided context. See [`ConfigParser::configure`] for information about context-sensitive parsing.                                                             |
