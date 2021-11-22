# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

# Unreleased

### Added

### Removed

### Changed

### Fixed

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
