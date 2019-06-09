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

## Testing
`cargo test`

## Contributing
The following are all welcome:
- code reviews
- issues/feature requests.
Note that feature requests should be limited to extensions or better error handling,
the compiler will not break backwards compatibility with C.
- test cases

There is not currently a code of conduct. Please do not do anything that would require me to make one.
