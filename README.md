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
