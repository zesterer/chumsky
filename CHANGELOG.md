# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

# Unreleased

### Added

### Removed

### Changed

### Fixed

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
