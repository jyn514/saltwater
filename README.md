# rcc

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

## Running

`cargo run` from top level directory.
Anything without loops or function pointers should work.
However, since there isn't a preprocessor, you need to declare library functions
manually using the declarations from the manpage.

Since varargs aren't implemented, you can't call `printf`.
Additionally, since there's no preprocessor, you can't `#include <stdio.h>`
and so can't call any function that requires a `FILE *`. This makes IO hard to do,
but it is possible using `puts` and `putchar`.

Try something like this:

```c
int puts(const char *s);
int putchar(char);

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
  puts("i is ");
  putchar('0' + j);
  putchar('\n');
  return j;
}

int g(int i) {
  if (i < 0 || i >= 3) {
    return 0;
  }
  return a[i];
}
```

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

## Reporting Bugs

If both `tcc` and `gcc` compile it and `rcc` doesn't, it's probably a bug.
If just `gcc` and `clang` (but not `tcc`) compile it, it's probably a compiler extension.
Use your own judgement, but please read the GCC documentation before saying an unimplemented extension is a bug.

If you find something `rcc` doesn't recognize (that's not a GCC extension), please report it,
including the code that doesn't work and the expected behavior in English (or at least pseudo-code).

If you find a panic ('thread main panicked at ...'), it's always a bug. Please report it!
The compiler is completely deterministic, so give at least one input that will crash it.
Smaller inputs are prefered but if you don't have time to minimize the test case that's fine.

If you find a miscompilation, it's a serious bug.
Please post the code as well as the expected and actual outputs.
I expect these bugs to be rare until I have more users
(not because the compiler isn't buggy, but because no one will notice the bugs).

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

Note that there should be a very strong reason to add new libraries to the project
because each new library increases the build time substantially,
making the compiler incrementally more frustrating to work on.

### Reference

You may find the following references useful.

#### Other projects

- [C11 Standard final draft](http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)
- [C99 Standard final draft](http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf)
- [C89 Standard final draft](https://www.pdf-archive.com/2014/10/02/ansi-iso-9899-1990-1/ansi-iso-9899-1990-1.pdf)
- [Yacc grammar for C11](http://www.quut.com/c/ANSI-C-grammar-y.html)
- [Lex grammar for C11](http://www.quut.com/c/ANSI-C-grammar-l-2011.html)
- [8cc](https://github.com/rui314/8cc), a self-hosting C compiler
- [tcc](https://github.com/LuaDist/tcc), a self-hosting C compiler originally [written for IOCCC](https://bellard.org/otcc/)

#### Documentation

- [cranelift_frontend::FunctionBuilder](https://docs.rs/cranelift-frontend/0.43.0/cranelift_frontend/struct.FunctionBuilder.html)
- [cranelift_codegen::InstBuilder](https://docs.rs/cranelift-codegen/0.43.0/cranelift_codegen/ir/trait.InstBuilder.html)
- [cranelift_module::Module](https://docs.rs/cranelift-module/0.43.0/cranelift_module/struct.Module.html)

## Code of Conduct

There is not currently a code of conduct. Please do not do anything that would require me to make one.
