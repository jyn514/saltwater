# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Fix pretty printing for exotic keywords (`_Noreturn`, ...)
- Make linking work on Windows, thanks to cranelift-object
- Change lots of error internals to make it an enum instead of a String
- Add instructions for building on Windows
- Fix incorrect description of arithmetic shift
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
