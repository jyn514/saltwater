# FAQ

## Why write a C compiler?

This is my third compiler.
The first one [is public](https://github.com/jyn514/lox), I started on it
because the lexer looked fun to write and kind of fell into the rest.
It's not useful to compile real code.
The second one is private, I wrote it for [a class](https://cse.sc.edu/~fenner/csce531/).
It compiled a very specific dialect of C and crashed on basically anything else.

I figured I would Rewrite It In Rust and do it right this time.
This is sort of the best of both worlds - I get the speed of C but the memory safety of Java/Python/Haskell.

## Are you planning on supporting obscure but standard features?

Yes. Variadic arguments are implemented (for callers),
functions with abstract parameter types are implemented,
functions without prototypes are [a work in progress](https://github.com/jyn514/rcc/tree/infer_fp_params),
structs, unions, and enums are all implemented (with bugs).

### Which C standard, exactly?

C11, although I also allow implicit int declarations (with a warning).

## Why use Cranelift instead of LLVM?

I actually tried LLVM to start using [Inkwell](https://github.com/TheDan64/inkwell)
but it [couldn't emit .o files](https://thedan64.github.io/inkwell/inkwell/object_file/struct.ObjectFile.html)
and I didn't want to call the FFI directly.
It also had a tendency to segfault on functions that were marked as safe.
See [this commit](https://github.com/jyn514/rcc/commit/9f5573d89d1bafcb56de8bee2387648e0cb015f3) for more context.
