# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.6.0] - 2020-02-25

### Added

- The preprocessor is working! It now supports
  - `#include` directives
  - `#define` directives, including function macros and cycle detection for object macros. Cycle detection for function macros is not implemented.
  - `#warning` and `#error` directives
  - `#if defined(var)` and `#elif`
See https://github.com/jyn514/rcc/issues/5 for a full list, including directives that aren't implemented.
- The `-E` option is also implemented. However, it doesn't include any newlines, so it's a little hard to read.
- Hex and octal character escapes (`'\x01'`). The null character escape is no longer special cased and is simply an octal escape.
- Added predefined macros for the host architecture and OS, as well as a few `__STDC*__` defines.
- Static data is now stored using `.bss` where possible. This avoids crashes on `int a[0xffffffff];`

### Changed

- Many fewer structs and functions are public. This allows removing unused code and also shouldn't affect library users since the exposed API wasn't particularly useful for anything except the parser.
- Errors now look like `<file>:2:1 error:` instead of `<stdin>:2:1: error:`
- Files must now end with a newline. Files not ending with a newline are a compile error (according to C11 they are undefined behavior: [5.1.1.2](http://port70.net/~nsz/c/c11/n1570.html#5.1.1.2))
- `rcc` will now panic instead of calling `std::process::exit` if an unrecoverable error occurs during codegen.
- Most dependencies (notably, excluding Cranelift) have been made optional to make `rcc` easier to use as a library.
- The top-level API looks significantly different. It now requires a `FileId` and a `Files` struct to allow for multiple files to be `#include`d. The `Opt` struct has also been made part of the library instead of the binary.

### Fixed

- Fixed crash on `switch (1) { case 1: case 1: }`
- Fixed crash on `void f() { int f; } int main() { f(); }`
- Fixed crash on `_Noreturn`
- Fixed _many_ of the bugs with `seen_line_token`, so this is no longer incorrectly marked as an error:

```c
#define a "b"
#define c "d"
```

### Removed

- The `CppError::Generic` variant has been removed in favor of specific error variants.

## [0.5.0] - 2020-02-07

### Added

- This release contains the start of a preprocessor.
It is in very early stages and will crash on any inputs other than
`#if`, `#else`, `#ifdef`, and `#endif`. I recommend using your host preprocessor until this one is further along.

- Added an error limit. Instead of overwhelming you with dozens of errors in a file with a misplaced `{`, rcc will now report at most 10 errors in one run. This can be configured with `--max-errors n`, see `rcc --help` for more details.

- Added a recursion limit. Now, rcc will exit with an error instead of crashing on highly nested inputs (200+ parenthesis in a row).

### Changed

- Fold `char` expressions, such as `'1' - '0'`
- Display characters properly in error messages (e.g. '1' instead of 49)
- Various additional `CompileError`s have been added. This allows inspecting the type of an error dynamically instead of having to blindly display the string.
- The `Compile` API now takes an `Opt` struct instead of 4 different parameters. This should make it easier to add more options in the future.
- Use Graham's name in the 'authors' field instead of his username

### Fixed

This release fixed many bugs found by [honggzfuzz](https://github.com/rust-fuzz/honggfuzz-rs). Thank you to @Byter09 for helping me get it set up as well as lending me CPU time for the fuzz runs!

- Fix crash on nested functions (`int f() { int g() {} }`)
- Fix crash on assignments other than identifiers and pointers (e.g. `++A[1]`)
- Fix _many_ crashes in constant folding. A giant thank you to @pythondude325 for redesigning and implementing the new interpreter!
- Fix crash on `return` in a `do-while` loop
- Fix crash on `int f(void, void)`, and `int f(void, i)`
- Fix crash on using typedefs in an expression context (`typedef int i; int j = i;`)
- Fix crash on label in switch without braces
- Fix crash on `!void`
- Fix crash on `(int)void`
- Fix crash on invalid syntax in an `if` statement (`if (1) {} else else`)
- Fix crash on `!(_Bool)1)`
- Fix crash on using invalid structs in an expression
- Fix crash on signed overflow when incrementing the counter used for `enum` constants (e.g. `enum { A = -1u, B }`)
- Fix crash on invalid break after switch
- Fix crash on aggregate initializers with misleading braces (`int a[][3] = {1,2,3};`). `rcc` now properly initializes this as `int a[1][3] = {{1,2,3}};`.
- Fix crash on unterminated string at the end of a file

And the non-crash fixes:

- Don't allow taking the address of `register` variables
- Don't allow assigning to `const` variables
- Remove backslashes before newlines

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
