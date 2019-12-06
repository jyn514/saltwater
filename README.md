# rcc

[![Build Status](https://travis-ci.org/jyn514/rcc.svg?branch=master)](https://travis-ci.org/jyn514/rcc)
![Minimum supported Rustc](https://img.shields.io/badge/rustc-1.37+-green.svg)
[Join us on Discord](https://discord.gg/2jRDZDU)

rcc: a Rust C compiler

A C compiler written in Rust, with a focus on good error messages. Warning: my first rust project, code quality is pretty low.

## Running

`cargo run` from top level directory.
You can also use `cargo run -- --debug-lex`, `cargo run -- --debug-ast`, `cargo run -- --debug-asm`
to show a very verbose description of the lexemes/AST/IR respectively.

Use `cargo run -- --help` for all options.

## TODO

- Preprocessor
- Fix boolean expressions
- Multiple translation units (files)
- Bitfields?
- Compile on Windows (see https://github.com/jyn514/rcc/issues/77)
- Compile on non-x86 platforms
- Cross-compile

## Testing

```sh
cargo test
# optionally, you can fuzz the compiler
# it may be more helpful to just `grep -R unimplemented src`, though
tests/fuzz.sh
```

## FAQ

See [FAQ.md](FAQ.md)

## Implementation Defined Behavior

See [IMPLEMENTATION\_DEFINED.md](IMPLEMENTATION_DEFINED.md)


## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).
This also includes reporting bugs.
