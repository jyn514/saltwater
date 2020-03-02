# Contributing

The following are all welcome:
- code reviews
- issues/feature requests.
Note that feature requests should be limited to extensions or better error handling,
the compiler will not break backwards compatibility with C.
- test cases

## Contributing Code

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

## Contributing Bug Reports

If you contribute a lot of bug reports, you may find the `.github/report-issue.sh` script useful.
It's used like so:

```
usage: ./report-issue.sh <issue type> <file> [-f]
```

`<issue type>` is the name of one of the issue templates, currently:

```
./report-issue.sh a README.md
unrecognized issue type (options are panic, codegen, parse), aborting
```

`<file>` is the path to the file with the relevant C source code.
`report-issue` will open your editor with a partially-filled out template, including a backtrace if appropriate.
After you close your editor, `report-issue` will open your browser to a 'new issue' GitHub page with the contents of the now-complete template.
You can still edit the issue browser if you like.

If you don't like this behavior of opening the browser,
you can instead run the script with `BROWSER=echo`
and it will print the URL instead.
Be aware that the URL contains the entire contents of the issue,
so it will be _very_ long.

If you want to run the script non-interactively, use `EDITOR=true`.

## Reference

You may find the following references useful.

### Other projects

- [C18 Standard final draft](https://web.archive.org/web/20191010011013/http://www2.open-std.org/JTC1/SC22/WG14/www/abq/c17_updated_proposed_fdis.pdf)
- [C11 Standard final draft](http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)
- [C99 Standard final draft](http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf)
- [C89 Standard final draft](https://www.pdf-archive.com/2014/10/02/ansi-iso-9899-1990-1/ansi-iso-9899-1990-1.pdf)
- [Yacc grammar for C11](http://www.quut.com/c/ANSI-C-grammar-y.html)
- [Lex grammar for C11](http://www.quut.com/c/ANSI-C-grammar-l-2011.html)
- [8cc](https://github.com/rui314/8cc), a self-hosting C compiler
- [tcc](https://github.com/LuaDist/tcc), a self-hosting C compiler originally [written for IOCCC](https://bellard.org/otcc/)

### Documentation

- [cranelift_frontend::FunctionBuilder](https://docs.rs/cranelift-frontend/0.43.0/cranelift_frontend/struct.FunctionBuilder.html)
- [cranelift_codegen::InstBuilder](https://docs.rs/cranelift-codegen/0.43.0/cranelift_codegen/ir/trait.InstBuilder.html)
- [cranelift_module::Module](https://docs.rs/cranelift-module/0.43.0/cranelift_module/struct.Module.html)

## Code of Conduct

There is not currently a code of conduct. Please do not do anything that would require me to make one.
