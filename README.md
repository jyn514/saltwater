# rcc

[![Build Status](https://travis-ci.org/jyn514/rcc.svg?branch=master)](https://travis-ci.org/jyn514/rcc)
[Join us on Discord](https://discord.gg/2jRDZDU)

rcc: a Rust C compiler

A C compiler written in Rust, with a focus on good error messages. Warning: my first rust project, code quality is pretty low

## TODO

- Preprocessor
- Multiple translation units (files)
- Parse switch statements
- Codegen for loops, switches, and gotos
- Implicit decay from arrays to pointers
- Variadic args (e.g. printf)
- Bitfields?
- Compile on Windows (see https://github.com/jyn514/rcc/issues/77)
- Compile on non-x86 platforms
- Cross-compile

## Running

`cargo run` from top level directory.
Anything without loops or function pointers should work.
However, since there isn't a preprocessor, you need to declare library functions
manually using the declarations from the manpage.

Since varargs aren't implemented, you can't call `printf`.
Additionally, since there's no preprocessor, you can't `#include <stdio.h>`
and so can't call any function that requires a `FILE *`. This makes IO hard to do,
but it is possible using `puts` and `putchar`.
There are examples in the 'examples' directory.

You can also use `cargo run -- --debug-lex`, `cargo run -- --debug-ast`, `cargo run -- --debug-asm`
to show a very verbose description of the lexemes/AST/IR respectively.

Use `cargo run -- --help` for all options.

## Testing

```sh
cargo test
# optionally, you can fuzz the compiler
# it may be more helpful to just `grep -R unimplemented src`, though
tests/fuzz.sh
```

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).
This also includes reporting bugs.
