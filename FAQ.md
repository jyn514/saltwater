# FAQ

## Why write a C compiler?

This is my third compiler.
The first one [is public](https://github.com/jyn514/lox), I started on it
because the lexer looked fun to write and kind of fell into the rest.
It's not useful to compile real code.
The second one is private, I wrote it for [a class](https://cse.sc.edu/~fenner/csce531/).
It compiled a very specific dialect of C and crashed on basically anything else.

I figured I would Rewrite It In Rust and do it write this time.

## Are you planning on supporting obscure but standard features?

Yes.

## Why use Cranelift instead of LLVM?

I actually tried LLVM to start using [Inkwell](https://github.com/TheDan64/inkwell)
but it [couldn't emit .o files](https://thedan64.github.io/inkwell/inkwell/object_file/struct.ObjectFile.html)
and I didn't want to call the FFI directly.
See [this commit](https://github.com/jyn514/rcc/commit/9f5573d89d1bafcb56de8bee2387648e0cb015f3) for more context.
