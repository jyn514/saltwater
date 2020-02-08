# rcc

[![Build Status](https://travis-ci.org/jyn514/rcc.svg?branch=master)](https://travis-ci.org/jyn514/rcc)
![Minimum supported Rustc](https://img.shields.io/badge/rustc-1.37+-green.svg)
[Join us on Discord](https://discord.gg/BPER7PF)

rcc: a Rust C compiler

A C compiler written in Rust, with a focus on good error messages. Warning: my first rust project, code quality is pretty low.

## Running

`cargo run` from top level directory.
You can also use `cargo run -- --debug-lex`, `cargo run -- --debug-ast`, `cargo run -- --debug-asm`
to show a very verbose description of the lexemes/AST/IR respectively.

Use `cargo run -- --help` for all options.

### Running on Windows

You need to have `cc` on your PATH. You can either install mingw + gcc or MSVC.
Other than that, it should work exactly the same as on Linux.

## TODO

- Preprocessor
- Fix boolean expressions
- Multiple translation units (files)
- Bitfields?
- Compile on non-x86 platforms
- Cross-compile

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
