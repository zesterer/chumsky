# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

# Unreleased

### Added

### Removed

### Changed

### Fixed

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
