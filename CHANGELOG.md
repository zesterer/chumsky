# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

# Unreleased

### Added

### Removed

### Changed

### Fixed

# [0.12.0] - 2025-12-15

### Added

- `MapExtra::emit`, which allows emitting secondary errors during mapping operations
- `InputRef::emit`, which allows emitting secondary errors within `custom` parsers
- `labelled_with`, which avoids the need to implement `Clone` for labels
- `Input::split_token_span`, a convenience function for splitting `(Token, Span)` inputs so that chumsky can understand them
- `Input::split_spanned`, which does the same as above, but for implementors of `WrappingSpan`
- `spanned`, a combinator which automatically annotates a parser output with a span
- Experimental:
    - `IterParser::parse_iter`, a way to turn an `IterParser` (like `x.repeated()`) into an iterator
    - `Parser::debug`, which provides access to various parser debugging utilities.

### Changed

- Made `nested_in` more flexible by allowing it to map between different input types instead of requiring the same input as the outer parser

### Fixed

- A prioritisation bug with `nested_in`

# [0.11.2] - 2025-11-05

### Added

- Implement `Default`, `PartialOrd`, and `Ord` for `SimpleSpan`
- Implement `PartialOrd` and `Ord` for `Rich`

# [0.11.1] - 2025-09-12

### Fixed

- Patched compilation error that only appeared in release builds

# [0.11.0] - 2025-09-11

### Added

- The `set(...)` combinator, which may be used to conveniently parse a set of patterns, in any order
- Support for non-associative infix operators are now supported by the `.pratt(...)` combinator
- `Parser::try_foldl`, allowing folding operations to short-circuit in a manner similar to `Parser::try_map`
- `Parser::contextual`, which allows a parser to be disabled or enabled in a context-sensitive manner
- Implemented `ValueInput` for `IterInput`, which was previously missing
- More types that implement the `State` trait:
    - `RollbackState`, which reverts parser state when a parser rewinds and may be used to, for example, count the number of times a pattern appears in the input
    - `TruncateState`, which truncates a vector when a parser rewinds, and may be used to implement an arena allocator for AST nodes
- Implemented `IterParser` for `a.then(b)` when both `a` and `b` are both `IterParser`s that produce the same output type

### Changed

- Made lifetime bounds on `recursive` and `ParserExtra` more permissive
- Improved support for grapheme parsing
- Text parsers now report labels
- `Parser::filter` now generates a `DefaultExpected::SomethingElse` label instead of nothing (this can be overridden with the `.labelled(...)` function)
- Improved areas of documentation
- Make whitespace parsers reject codepoints that are vulnerable to [CVE-2021-42574](https://www.cve.org/CVERecord?id=CVE-2021-42574)
- Maybe the `select!` parser more permissive, accepting any implementor of `Input` instead of requiring `ValueInput` too

### Fixed

- Many minor incorrect debug-only sanity checks have been fixed
- Many minor span and error prioritisation behavioural problems have been fixed (most notably, `Parser::try_map`)
- The `.rewind()` parser no longer rewinds any secondary error that were encountered
- Accidental `text::ascii::keyword` lifetime regression

# [0.10.1] - 2025-04-13

### Added

- Implemented `Container` for `VecDeque`
- New section covering recursion in the guide

### Changed

- `Boxed` types now have a default type parameter of `extra::Default`, like `Parser` and `IterParser`
- The tutorial has been updated for `0.10` and has been moved to the guide

### Fixed

- Nonsense spans occasionally generated for non-existent tokens
- Improved docs have been added for several items
- Many minor documentation issues have been fixed

# [0.10.0] - 2025-03-22

*Note: version 0.10 is a from-scratch rewrite of chumsky with innumerable small changes. To avoid this changelog being
longer than the compiled works of Douglas Adams, the following is a high-level overview of the major feature additions
and does not include small details.*

### Added

- Support for zero-copy parsing (i.e: parser outputs that hold references to the parser input)
- Support for parsing nested inputs like token trees
- Support for parsing context-sensitive grammars such as Python-style indentation, Rust-style raw strings, and much
more
- Support for parsing by graphemes as well as unicode codepoints
- Support for caching parsers independent of the lifetime of the parser
- A new trait, `IterParser`, that allows expressing parsers that generate many outputs
- Added the ability to collect iterable parsers into fixed-size arrays, along with a plethora of other container types
- Support for manipulating shared state during parsing, elegantly allowing support for arena allocators, cstrees,
interners, and much more
- Support for a vast array of new input types: slices, strings, arrays, `impl Read`ers, iterators, etc.
- Experimental support for memoization, allowing chumsky to parse left-recursive grammars and reducing the
computational complexity of parsing certain grammars
- An extension API, allowing third-party crates to extend chumsky's capabilities and introduce new combinators
- A `pratt` parser combinator, allowing for conveniently and simply creating expression parsers with precise operator
precedence
- A `regex` combinator, allowing the parsing of terms based on a specific regex pattern
- Properly differentiated ASCII and Unicode text parsers

## Removed

- `Parser::then_with` has been removed in favour of the new context-sensitive combinators

### Changed

- Performance has *radically* improved
- Error generation and handling is now significantly more flexible

# [0.9.2] - 2023-03-02

### Fixed

- Properly fixed `skip_then_retry_until` regression

# [0.9.1] - 2023-03-02

### Fixed

- Regression in `skip_then_retry_until` recovery strategy

# [0.9.0] - 2023-02-07

### Added

- A `spill-stack` feature that uses `stacker` to avoid stack overflow errors for deeply recursive parsers
- The ability to access the token span when using `select!` like `select! { |span| Token::Num(x) => (x, span) }`
- Added a `skip_parser` recovery strategy that allows you to implement your own recovery strategies in terms of other
  parsers. For example, `.recover_with(skip_parser(take_until(just(';'))))` skips tokens until after the next semicolon
- A `not` combinator that consumes a single token if it is *not* the start of a given pattern. For example,
  `just("\\n").or(just('"')).not()` matches any `char` that is not either the final quote of a string, and is not the
  start of a newline escape sequence
- A `semantic_indentation` parser for parsing indentation-sensitive languages. Note that this is likely to be
  deprecated/removed in the future in favour of a more powerful solution
- `#[must_use]` attribute for parsers to ensure that they're not accidentally created without being used
- `Option<Vec<T>>` and `Vec<Option<T>>` now implement `Chain<T>` and `Option<String>` implements `Chain<char>`
- `choice` now supports both arrays and vectors of parsers in addition to tuples
- The `Simple` error type now implements `Eq`

### Changed

- `text::whitespace` returns a `Repeated` instead of an `impl Parser`, allowing you to call methods like `at_least` and
  `exactly` on it.
- Improved `no_std` support
- Improved examples and documentation
- Use zero-width spans for EoI by default
- Don't allow defining a recursive parser more than once
- Various minor bug fixes
- Improved `Display` implementations for various built-in error types and `SimpleReason`
- Use an `OrderedContainer` trait to avoid unexpected behaviour for unordered containers in combination with `just`

### Fixed

- Made several parsers (`todo`, `unwrapped`, etc.) more useful by reporting the parser's location on panic
- Boxing a parser that is already boxed just gives you the original parser to avoid double indirection
- Improved compilation speeds

# [0.8.0] - 2022-02-07

### Added

- `then_with` combinator to allow limited support for parsing nested patterns
- impl From<&[T; N]> for Stream
- `SkipUntil/SkipThenRetryUntil::skip_start/consume_end` for more precise control over skip-based recovery

### Changed

- Allowed `Validate` to map the output type
- Switched to zero-size End Of Input spans for default implementations of `Stream`
- Made `delimited_by` take combinators instead of specific tokens
- Minor optimisations
- Documentation improvements

### Fixed

- Compilation error with `--no-default-features`
- Made default behaviour of `skip_until` more sensible

# [0.7.0] - 2021-12-16

### Added

- A new [tutorial](tutorial.md) to help new users

- `select` macro, a wrapper over `filter_map` that makes extracting data from specific tokens easy
- `choice` parser, a better alternative to long `or` chains (which sometimes have poor compilation performance)
- `todo` parser, that panics when used (but not when created) (akin to Rust's `todo!` macro, but for parsers)
- `keyword` parser, that parses *exact* identifiers

- `from_str` combinator to allow converting a pattern to a value inline, using `std::str::FromStr`
- `unwrapped` combinator, to automatically unwrap an output value inline
- `rewind` combinator, that allows reverting the input stream on success. It's most useful when requiring that a
  pattern is followed by some terminating pattern without the first parser greedily consuming it
- `map_err_with_span` combinator, to allow fetching the span of the input that was parsed by a parser before an error
  was encountered

- `or_else` combinator, to allow processing and potentially recovering from a parser error
- `SeparatedBy::at_most` to require that a separated pattern appear at most a specific number of times
- `SeparatedBy::exactly` to require that a separated pattern be repeated exactly a specific number of times
- `Repeated::exactly` to require that a pattern be repeated exactly a specific number of times

- More trait implementations for various things, making the crate more useful

### Changed

- Made `just`, `one_of`, and `none_of` significant more useful. They can now accept strings, arrays, slices, vectors,
  sets, or just single tokens as before
- Added the return type of each parser to its documentation
- More explicit documentation of parser behaviour
- More doc examples
- Deprecated `seq` (`just` has been generalised and can now be used to parse specific input sequences)
- Sealed the `Character` trait so that future changes are not breaking
- Sealed the `Chain` trait and made it more powerful
- Moved trait constraints on `Parser` to where clauses for improved readability

### Fixed

- Fixed a subtle bug that allowed `separated_by` to parse an extra trailing separator when it shouldn't
- Filled a 'hole' in the `Error` trait's API that conflated a lack of expected tokens with expectation of end of input
- Made recursive parsers use weak reference-counting to avoid memory leaks

# [0.6.0] - 2021-11-22

### Added

- `skip_until` error recovery strategy
- `SeparatedBy::at_least` and `SeparatedBy::at_most` for parsing a specific number of separated items
- `Parser::validate` for integrated AST validation
- `Recursive::declare` and `Recursive::define` for more precise control over recursive declarations

### Changed

- Improved `separated_by` error messages
- Improved documentation
- Hid a new (probably) unused implementation details

# [0.5.0] - 2021-10-30

### Added

- `take_until` primitive

### Changed

- Added span to fallback output function in `nested_delimiters`

# [0.4.0] - 2021-10-28

### Added

- Support for LL(k) parsing
- Custom error recovery strategies
- Debug mode
- Nested input flattening

### Changed

- Radically improved error quality
