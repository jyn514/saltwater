# rust-c-compiler
A C compiler written in Rust, with a focus on good error messages. Warning: my first rust project, code quality is pretty low

## Implemented
- Lexer
- Declarations (`int i, *p;`)
- Some error handling
- Some command line arguments
- ... not much else ...

## TODO
- Preprocessor
- Expressions
- Statements (besides declarations)
- Multiple translation units (files)
- Codegen (probably to a MIR) - want to match GCC calling convention to allow linking to glibc.
- Optimization?
- Assembly/Linking

## Running
`cargo run` from top level directory.
Not much works yet, but you can try `static unsigned long *const (*l)(int []);`.
You can also use `cargo run -- - -d` to show every token the lexer found.

## Testing
`cargo test`

## Contributing
The following are all welcome:
- code reviews
- issues/feature requests.
Note that feature requests should be limited to extensions or better error handling,
the compiler will not break backwards compatibility with C.
- test cases

Substantial new features (e.g. expression parsing) may not be accepted at this point,
since this is a side project and I do kind of want to write the code myself.
Bugfixes and minor features (e.g. better error messages) are welcome, please submit a pull request.

If you do submit a patch, please write at least one or two test cases.
Rust convention is to put them in a `tests` module with `#[test]` in front of the function,
which makes them automatically run with `cargo test`.
See the end of `src/lex.rs` for an example.

Patches will not be merged unless they pass all current tests, including `clippy` and `rustfmt`.
You can run these with `./test.sh`; I suggest sym-linking it to `.git/hooks/pre-commit`.

## Code of Conduct

There is not currently a code of conduct. Please do not do anything that would require me to make one.
