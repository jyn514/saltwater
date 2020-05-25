# rcc

[![Build Status](https://travis-ci.org/jyn514/rcc.svg?branch=master)](https://travis-ci.org/jyn514/rcc)
[Join us on Discord](https://discord.gg/BPER7PF)

rcc: a Rust C compiler

A C compiler written in Rust, with a focus on good error messages.
Warning: my first rust project, code quality is pretty low.

## Running

`rcc` reads from standard in by default, so you can type in code directly.
It's not interactive though, you have to hit Ctrl+D to indicate end of file (Ctrl+Z on Windows).

Use `rcc --help` for all options (or see [below](#all-options)).

### Running on Windows

You need to have `cc` on your PATH. You can either install mingw + gcc or MSVC.
Other than that, it should work exactly the same as on Linux.

## Unimplemented features

- Defining functions taking variadic arguments. Note that calling variadic functions (like `printf`) is already supported.
- Variable-length arrays (`int a[n]`)
- Multiple translation units (files)
- Bitfields
- Compiling on non-x86 platforms
- Cross-compilation

## Examples

```c
$ cat tests/runner-tests/readme.c
// output: j is 6
int printf(const char *, ...);

typedef struct s *sp;

int i = 1;
int a[3] = {1, 2, 3};
float f = 2.5;

struct s {
  int outer;
} my_struct;

int g(int);

int main(void) {
  sp my_struct_pointer = &my_struct;
  const int c = my_struct_pointer->outer = 4;
  // should return 6
  int j = i + f*a[2] - c/g(1);
  printf("j is %d\n", j);
  return j;
}

int g(int i) {
  if (i < 0 || i >= 3) {
    return 0;
  }
  return a[i];
}
$ rcc tests/runner-tests/readme.c
$️ ./a.out
j is 6
```

### Debug output

```c
$ cat tests/runner-tests/cpp/if/defined.c
// code: 2

#define a
#define b

#if defined(a)
int i = 2;
#endif

#ifndef b
syntax error
#endif

# if defined b && defined(a)
    int main() { return i; }
#endif
$ rcc -E tests/runner-tests/cpp/if/defined.c
int i = 2 ; int main ( ) { return i ; }
```

```c
$ echo 'int i = 1 + 2 ^ 3 % 5 / 2 & 1; int main(){}' | rcc --debug-ast
ast: int i = ((1) + (2)) ^ ((((3) % (5)) / (2)) & (1));
ast: int main(){
}
```

```c
$ cat tests/runner-tests/hello_world.c
#include<stdio.h>
int main() {
    puts("Hello, world!");
}
$ rcc --debug-ir tests/runner-tests/hello_world.c
function u0:0() -> i32 system_v {
    gv0 = symbol colocated u1:3
    sig0 = (i64) -> i32 system_v
    fn0 = u0:26 sig0

block0:
    v0 = global_value.i64 gv0
    v1 = call fn0(v0)
    v2 = iconst.i32 0
    return v2
}
$ ./a.out
Hello, world!
```

### All options

```txt
$ rcc --help
rcc 0.9.0
Joshua Nelson <jyn514@gmail.com>
A C compiler written in Rust, with a focus on good error messages.
Homepage: https://github.com/jyn514/rcc/

usage: rcc [FLAGS] [OPTIONS] [<file>]

FLAGS:
        --debug-ast        If set, print the parsed abstract syntax tree (AST) in addition to compiling.
                            The AST does no type checking or validation, it only parses.
        --debug-hir        If set, print the high intermediate representation (HIR) in addition to compiling.
                            This does type checking and validation and also desugars various expressions.
        --debug-ir         If set, print the intermediate representation (IR) of the program in addition to compiling.
        --debug-lex        If set, print all tokens found by the lexer in addition to compiling.
        --jit              If set, will use JIT compilation for C code and instantly run compiled code (No files produced).
                            NOTE: this option only works if rcc was compiled with the `jit` feature.
    -h, --help             Prints help information
    -c, --no-link          If set, compile and assemble but do not link. Object file is machine-dependent.
    -E, --preprocess-only  If set, preprocess only, but do not do anything else.
                            Note that preprocessing discards whitespace and comments.
                            There is not currently a way to disable this behavior.
    -V, --version          Prints version information

OPTIONS:
        --color <when>       When to use color. May be "never", "auto", or "always". [default: auto]
    -o, --output <output>    The output file to use. [default: a.out]
        --max-errors <max>   The maximum number of errors to allow before giving up.
                             Use 0 to allow unlimited errors. [default: 10]
    -I, --include <dir>      Add a directory to the local include path (`#include "file.h"`).
                              Can be specified multiple times to add multiple directories.
    -D, --define <id[=val]>  Define an object-like macro.
                              Can be specified multiple times to add multiple macros.
                              `val` defaults to `1`.

ARGS:
    <file>    The file to read C source from. "-" means stdin (use ./- to read a file called '-').
              Only one file at a time is currently accepted. [default: -]
```

## Testing

```sh
cargo test
# optionally, you can fuzz the compiler
# it may be more helpful to just `grep -R unimplemented src`, though

# libFuzzer/AFL
tests/fuzz.sh

# Honggfuzz:
# Running Honggfuzz locally requires some parameters to use it at its full potential,
# so it is probably a good idea to have a look here: https://github.com/rust-fuzz/honggfuzz-rs/blob/master/README.md
# and here: https://github.com/google/honggfuzz/blob/master/docs/USAGE.md
# we suggest the following:
HFUZZ_RUN_ARGS="--tmout_sigvtalrm --exit_upon_crash" tests/hfuzz.sh
```

## FAQ

See [FAQ.md](FAQ.md)

## Implementation Defined Behavior

See [IMPLEMENTATION\_DEFINED.md](IMPLEMENTATION_DEFINED.md)

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).
This also includes reporting bugs.
