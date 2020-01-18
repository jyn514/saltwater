# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.4.0] - 2020-01-18

### Added

- Add spans and pretty-printing for errors. Now you actually know where the error is coming from!
- `impl PartialOrd for Location`

### Changed

- The `Parser::new()` API is now simpler and yet harder to use. The `Lexer::first_token()` API has been added to make up for it.
- Redo errors again, hopefully for the last time
- Updated to Cranelift 0.54

### Fixed

- Fix stack overflow when printing an error with a '='
- Fix several ICEs on invalid inputs thanks to `cargo fuzz`
- Fix deadlock in single-threaded process. This is exactly as bad as it sounds, see https://github.com/jyn514/rcc/commit/2b6bc7e349b6c880325d65cea6097d7f6876ed2f for details.
- Fix incorrect printing for keywords

### Removed

- Removed unnecessary dependency on `hexf`; now we only use `hexf_parse`

## [0.3.0] - 2020-01-10

### Changed

- Change lots of error internals to make it an enum instead of a String

### Fixed

- Fix pretty printing for exotic keywords (`_Noreturn`, ...)
- Fix incorrect description of arithmetic shift

### Added

- Make linking work on Windows, thanks to cranelift-object
- Add instructions for building on Windows
- Parse (and discard) `inline` keyword
- Parse (and discard) bitfields
- Implement pointers to character literals (https://github.com/jyn514/rcc/issues/146)

## [0.2.0] - 2019-12-06

### Added

- struct initializers
- struct assignment
- [static n] in function parameters

### Changed

- Require union initializers to have a surrounding `{}`

### Fixed

- Re-added --version flag
- Crash at link time on large stack allocation (https://github.com/bytecodealliance/cranelift/issues/1263)
- Scoping for struct declarations (https://github.com/jyn514/rcc/issues/88)
- Segfault at runtime for struct dereferences (https://github.com/jyn514/rcc/issues/103)

## [0.1.0] - 2019-11-29

Initial publish to crates.io
