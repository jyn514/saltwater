# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

This release is the first time that `saltwater` can compile hello world without any workaround on a GNU libc platform!
Previously, the following would give an error on Ubuntu 20.04:

```c
#include<stdio.h>

int main() {
    puts("Hello, world!");
}
stdio.h:33:2 error: invalid macro: file 'stddef.h' not found
#include <stddef.h>
 ^^^^^^^^^^^^^^^^^^
stdio.h:36:2 error: invalid macro: file 'stdarg.h' not found
#include <stdarg.h>
 ^^^^^^^^^^^^^^^^^^
```

This error was because glibc expects certain header files to be part of the compiler,
not part of the standard library. Since `saltwater` does not come packaged with any
header files, it would be unable to find them on disk.

Now, `saltwater` comes with `stddef.h` and `stdarg.h` built-in,
and it is simple to extend it to add more built-in headers. If you run into other
errors of this sort (standardized headers only please),
feel free to file a bug and they can be added!

### Changed

- [#477] Get rid of `first` argument to `Parser::new`, making the API easier to use.
- `LexError::MultiCharCharLiteral` was renamed to `MultiByteCharLiteral`. See [#468] below.
- Cranelift has been updated to 0.66.
- [#448] `git-testament` is now optional and disabled by default. This should reduce compile times slightly.

### Fixed

- [#468] Don't panic on unicode characters.
  Note that Unicode identifiers still aren't allowed, they just give a nice error message instead of panicking.

- [#480] Don't require `codespan-reporting`.
  The dependency was unused.

### Added

- [#479] `Opt` now derives `Clone`.
- [#485] Document how to install `saltwater` via homebrew. Thank you to @SeekingMeaning for the PR!
- [#487] `stddef.h` and `stdarg.h` are now built-in header files.
  If the standard library packages stddef.h (e.g. on Alpine) that file will be used;
  otherwise, saltwater will use the built-in files.

[#448]: https://github.com/jyn514/saltwater/pull/448
[#468]: https://github.com/jyn514/saltwater/pull/468
[#477]: https://github.com/jyn514/saltwater/pull/477
[#479]: https://github.com/jyn514/saltwater/pull/479
[#480]: https://github.com/jyn514/saltwater/pull/480
[#485]: https://github.com/jyn514/saltwater/pull/485
[#487]: https://github.com/jyn514/saltwater/pull/487

## [0.10.0] - 2020-06-07

### Changed

- `rcc` has been renamed to `saltwater`! See https://github.com/jyn514/rcc/pull/460 for details on why. The new binary name is `swcc`.
- `saltwater` no longer requires a `Files` and `FileId` struct to construct a preprocessor.
  Instead, the preprocessor has a new `into_files()` method which allows you to recover the files for later use,
  and the main `compile` method returns a `Program` struct which contains the files.
  This makes it significantly easier to use the API if you don't need the files.
- `saltwater` now uses `lasso` instead of `string-interner`. lasso is ~50% faster than string-interner ([benchmarks](https://docs.rs/lasso/0.2.2/lasso/#benchmarks)) and does not have the UB that string-interner currently does ([string-interner#15](https://github.com/Robbepop/string-interner/issues/15)). Giant thanks to @kixiron for not only making the PR, but writing lasso from scratch!
- `cranelift` has been updated from 0.63 to 0.64.

### Added

- The `Analyzer` has been separated out into `Analyzer` and `PureAnalyzer`. `Analyzer` is an iterator, while `PureAnalyzer` is not. The pure version is useful if you want to compile a single expression or statement instead of many at once.
- `saltwater` now has whitespace tokens! This means that `-E` will keep all whitespace from the original file. Thank you to @hdamron for designing and implementing this!
- `InternedStr::is_empty` has been added.
- There is now a `replace` module separate from the preprocessor itself.
  This allows replacing specific tokens without preprocessing the entire file. In particular, it means you can input `Token`s instead of needing the original `&str`.

### Fixed

- The semver requirements have been fixed. `saltwater` now states that it requires `proptest >= 0.9.6`.
- Don't give warnings when compiling with `--no-default-features`.
- Don't loop forever on mutual recursion in function macros ([#399](https://github.com/jyn514/saltwater/issues/399), [#427](https://github.com/jyn514/saltwater/issues/427))
- Don't give an error for `1.0/0` and `0.0/0`,
  which should evaluated to `INF` and `NaN`, respectively.
- Don't give an error for function macros with no arguments ([#450](https://github.com/jyn514/saltwater/issues/450)).
- Correctly give an error when an `#if` expression has trailing tokens. For example, this code would previously compile without warnings:
```c
#if 1+2;
#endif
<stdin>:2:4 error: invalid macro: trailing tokens in `#if` expression
#if 1+2;
   ^^^^^
```
- Correctly give an error when a macro is redefined. For example, this code would previously compile without warnings:
```c
#define a b
#define a c
<stdin>:2:2 error: invalid macro: redefinition of 'a' does not match original definition
#define a c
 ^^^^^^^^^^
```

## [0.9.0] - 2020-05-11

### Added

- `rcc` now has a feature-flag for code generation.
If you only need to parse C code without generating a binary,
you can add `default-features = false` to `Cargo.toml`, which avoids having to compile all of cranelift.

- `rcc` now allows setting macros on the command line with `-D`.
  The syntax is intentionally as close to Clang as possible, but works differently internally:
  if the macro consists of invalid tokens (e.g. `rcc -D 'a=@'`),
  it will give an error immediately instead of waiting until macro replacement occurs.
  See `rcc -h` for the syntax or `rcc --help` for a full description.

- Added a `--color` option so that `rcc` will no longer always print errors in color.
  Thank you to @pythondude for working on this!

- Added a `--debug-hir` option which has the effect of the old `--debug-ast` flag.
  `--debug-ast` now prints only the parsed code without performing type checking or validation.

- Added documentation for `runner-tests`

### Changed

- The minimum supported Rust version (MSRV) has been removed.
  Cranelift does not have a MSRV and it made no sense for rcc to test for versions
  when it has no control over the supported version.

- The parser and analyzer have been split into different modules ([#151](https://github.com/jyn514/rcc/issues/151)).
  This fixed many different bugs and also came with a lot of performance improvements;
  see [!370](https://github.com/jyn514/rcc/pull/370) for a full list.

  In particular, this now uses a pratt-parser instead of full-recursive descent,
  so it uses much less stack space to parse expressions. As a result, rcc can now parse
  over 10,000 nested expressions in a row (e.g. something like `((((((((1)))))))))`).
  Additionally, unary expressions are now parsed iteratively instead of recursively,
  so `******p` will not overflow in the parser regardless of the number of dereferences
  (it will still overflow in the analyzer if you have several thousand dereferences).

- Spans are now merged properly! Before, errors would only point to a single token, like so:
```c
int *p = 4.0 + 1;
<stdin>:1:14 error: invalid program: cannot implicitly convert 'double' to 'int *'. help: use an explicit cast: (int *)
int *p = 4.0 + 1;
             ^
```
  Now, the span shows the entire expression:
```c
int *p = 4.0 + 1;
<stdin>:1:10 error: invalid program: cannot implicitly convert 'double' to 'int *'. help: use an explicit cast: (int *)
int *p = 4.0 + 1;
         ^^^^^^^
```

- The `compile` function (and similar in `lib.rs`) now takes `Opt` instead of `&Opt` (to support custom defines).
- `color-backtrace` can now be disabled if you don't use it.
- The `log` and `serde` dependencies have been removed.
- Cranelift has been updated to 0.63.


### Fixed

- Compound assignment (`+=`) has been fixed! Previously, `rcc` was very fragile about how it handled 
  compound assignment; the type checking was not always correct and it would sometimes panic.
  See [#244](https://github.com/jyn514/rcc/issues/244), [#214](https://github.com/jyn514/rcc/issues/214),
  [#121](https://github.com/jyn514/rcc/issues/121) for examples of the previous bugs.
  Now, compound assignment [almost always](https://github.com/jyn514/rcc/issues/393) works correctly.

- The pretty-printing for nested pointers has been fixed.
  Previously, `char **p` would be parsed successfully, but printed as `char (*)*p`.
  It now prints correctly as `char **p`. Thank you to @pythondude for working on this!
  See [!407](https://github.com/jyn514/rcc/pull/407) for more details.

  TODO: fix AST printing, it only fixed HIR printing

- `rcc` now allows function declarations to add or remove a qualifier,
  since it does not affect the definition ([#346](https://github.com/jyn514/rcc/issues/346)).
  Before, it would erroneously give an error for this code:
  ```c
  int f(int i);
  int f(const int i) { return i; }
  <stdin>:2:6 error: invalid program: redeclaration of 'f' with different type or qualifiers (originally extern int f(int i), now extern int f(int i))
  ```

- Functions now properly decay to function pointers in arguments: `int f(int g())` -> `int f(int (*g)())`
  ([#142](https://github.com/jyn514/rcc/issues/142)).
  Thank you to @hdamron for working on this!
- `int f(int ())` now correctly parses as 'function taking function returning int' ([#141](https://github.com/jyn514/rcc/issues/141))
- The preprocessor detects cycles for function-like macros with more than one token ([#312](https://github.com/jyn514/rcc/issues/312))
  There are currently no known issues with cycle detection.
- The preprocessor allows arguments to function-like macros to contain parentheses ([#354](https://github.com/jyn514/rcc/issues/354))
- The preprocessor now performs macro replacement for identifiers in `#elif` directives ([#387](https://github.com/jyn514/rcc/issues/387))
- Fixed regression from 0.7 where strings would not be concatenated if there was a newline in between ([#350](https://github.com/jyn514/rcc/issues/350))
- When using `--debug-ast`, declarations are no longer printed twice ([!423](https://github.com/jyn514/rcc/pull/423)).
- The `rcc` binary now says the correct number of warnings and errors printed.
  Before, it would always say there were as many warnings as errors.
- Several panics have been fixed:
    - [#282](https://github.com/jyn514/rcc/issues/282)
    - [#339](https://github.com/jyn514/rcc/issues/339)
    - [#404](https://github.com/jyn514/rcc/issues/404)

## [0.8.0] - 2020-03-14

### Added

- A new `PreProcessorBuilder` API has been exposed. This API allows you to construct a preprocessor without passing in every option explicitly, which gives a much more stable API (`PreProcessor::new` changes its signature regularly).

### Changed

- @pythondude325 has written a crate ([`hexponent`](https://crates.io/crates/hexponent)) for parsing hexadecimal floats!
This crate has replaced hexf.
As a result, rcc no longer panics on `0x.000000000000000000102`.

- `rcc` now exports the `codespan` library.
If you need to use it downstream, you can use the version exported by rcc.
This is of special importance because the `PreProcessor` takes a `FileId` defined by codespan.

- `rcc` no longer errors on the following code ([#311](https://github.com/jyn514/rcc/issues/311)):
```c
static int f();
int f();
```

- The `LexError::Generic` field has been removed.
All lex errors now have a specific cause that can be inspected at runtime.
Future errors will also have a specific cause.

### Fixed

- The lexer no longer goes into an infinite loop on `//` without a following newline at the end of a file ([#323](https://github.com/jyn514/rcc/issues/323))
- @Byter09 fixed a crash on array sizes that overflowed ([#327](https://github.com/jyn514/rcc/pull/327))

## [0.7.0] - 2020-03-06

### Added

- rcc now has a Just-In-Time compiler (JIT)!
This feature is turned off by default as it adds a dependency on `cranelift-simplejit`.
To use it, add `features = ["jit"]` to your `Cargo.toml`.
As a side effect, rcc now has proper benchmarks using in-memory compilation to avoid noise from IO.
A giant thank you to @playx for implementing this!

- The `-I` flag has been implemented. No more will you have to play silly games with symbolic links!
(See `--help` for a full description)

- There is now a `.github/report-issue.sh` script in case you report issues a lot.
See `CONTRIBUTING.md` for more details as well as how to use it.

### Changed

- The long-neglected README has been updated to reflect the currently implemented features and TODOs.

### Fixed

- rcc no longer crashes on structs where the size without padding is not a multiple of the alignment
([#278](https://github.com/jyn514/rcc/issues/278). Thanks to @repnop for fixing this!
- rcc no longer crashes on many unary operators in a row ([#329](https://github.com/jyn514/rcc/pull/329))
- The README proclaims support for 1.37, but the preprocessor in 0.6 used features from 1.40.
This release rewrote those changes in a way that's backwards-compatible with 1.37.
Merges to master have now been gated on the 1.37 build succeeding to avoid accidents like this in the future.
- More cycle detection has been implemented ([#293](https://github.com/jyn514/rcc/issues/298)).
For example, the following code no longer goes into an infinite loop:

```c
// from real code in <signal.h> !!
#define sa_handler   __sa_handler.sa_handler
#define sa_sigaction __sa_handler.sa_sigaction
int main() {
    struct sigaction handler;
    handler.sa_handler = 0;
}
```

However, function macros which expand to themselves will still loop forever ([#312](https://github.com/jyn514/rcc/issues/312)).

- `*p;` now gives a warning that the type of `p` defaults to `int *`. Thank you to @repnop for implementing this.

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
