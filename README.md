# rcc

rcc: a Rust C compiler

A C compiler written in Rust, with a focus on good error messages. Warning: my first rust project, code quality is pretty low

## Implemented

- Lexer
- Declarations (`int i, *p;`)
- Binary expressions (+, -, \*, /, \<, \>, \<\<, \>\>, ==, !=)
- Implicit binary conversions (1.0 == 1)
- Basic static initialization (i64, f64, arrays)
- Scalar dynamic initialization (`int i = 1` inside a function)
- Local variables; loads and stores
- Compiling to object files on x86_64
- Linking using host `cc` (similar to how the rust compiler does it)
- Some error handling
- Some command line arguments

## TODO

- Preprocessor
- Multiple translation units (files)
- Parse switch statements
- Codegen for statements
- Scoping for variables
- Structs, Unions, Enums
- Bitfields?
- pointer arithmetic (including arrays)

## Running

`cargo run` from top level directory.
Anything without pointers or control flow should work, try something like this:

```c
int i = 1;
int a[3] = {1, 2, 3};
float f = 2.5;

int main(void) {
  const int c = 4;
  // should return 6
  return i + f*a[2] - c/a[1];
}
```

You can also use `cargo run -- --debug-lex` or `cargo run -- --debug-ast`
to show a very verbose description of the lexemes/AST respectively.

Use `cargo run -- --help` for all options.

## Testing

```sh
cargo test
# optionally, you can fuzz the compiler
# it may be more helpful to just `grep -R unimplemented src`, though
cargo +nightly fuzz run libfuzzer -- -timeout=1
cd fuzz && {
  RUSTFLAGS="-Clink-arg=-fuse-ld=gold" cargo afl build --bin afl &&
  AFL_SKIP_CPUFREQ=1 cargo afl fuzz -i afl/inputs -o afl/outputs target/debug/afl
}
```

## Contributing

The following are all welcome:
- code reviews
- issues/feature requests.
Note that feature requests should be limited to extensions or better error handling,
the compiler will not break backwards compatibility with C.
- test cases

Substantial new features (e.g. a preprocessor) may not be accepted at this point,
since this is a side project and I do kind of want to write the code myself.
Bugfixes and minor features (e.g. better error messages) are welcome, please submit a pull request.

If you do submit a patch, please write at least one or two test cases.
Rust convention is to put them in a `tests` module with `#[test]` in front of the function,
which makes them automatically run with `cargo test`.
See the end of `src/lex.rs` for an example.

Patches will not be merged unless they pass all current tests, including `clippy` and `rustfmt`.
You can run these with `tests/pre-commit.sh`;
I suggest sym-linking it to `.git/hooks/pre-commit` like this:
`ln -s ../../tests/pre-commit.sh .git/hooks/pre-commit`.

## Code of Conduct

There is not currently a code of conduct. Please do not do anything that would require me to make one.
