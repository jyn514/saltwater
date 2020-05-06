# Contributing

The following are all welcome:
- code reviews
- issues/feature requests.
Note that feature requests should be limited to extensions or better error handling,
the compiler will not break backwards compatibility with C.
- test cases

## Contributing Code

Bugfixes and minor features (e.g. better error messages) are welcome,
please submit a pull request.

If you would like to work on a larger feature,
either comment on an existing issue, make a new issue,
or discuss it in the discord to make sure you know how to get started.

If you do submit a patch, please write at least one or two test cases.
You can either write unit tests or runner tests, described below.

Patches will not be merged unless they pass all current tests, including `clippy` and `rustfmt`.
You can run these with `tests/pre-commit.sh`;
I suggest sym-linking it to `.git/hooks/pre-commit` like this:
`ln -s ../../tests/pre-commit.sh .git/hooks/pre-commit`.

Note that new dependencies are frowned upon
because each new library increases the build time,
making the compiler incrementally more frustrating to work on.

### Unit tests

Rust convention for unit tests is to put them in a `tests` module
with `#[test]` in front of the function,
which makes them automatically run with `cargo test`.
See the end of `src/lex.rs` for an example.

### Runner tests

Writing unit tests for nested types can get tedious very quickly.
Writing unit tests for codegen is not really possible,
since we want to see how the program behaves at runtime,
and running arbitrary C code in-process is a recipe for disaster.

Instead, rcc uses 'Runner tests', which are C files in
`tests/runner-tests` that are compiled and run by `tests/runner.rs`.
You can control the expected output using a comment at the top of the file
(usually something like `// succeeds` or `code: 1`).
See [`runner.rs:run_one`](https://github.com/jyn514/rcc/blob/697dd04f1e838d63b35a848ead3222750111f041/tests/runner.rs#L31)
for a full list of options.
See `tests/runner-tests` for examples of existing tests.

### Input minimizer

In `minimizer/` is a script wrapping [DustMite](https://github.com/CyberShadow/DustMite)
which can be used to minimize any C file using some simple conditions.
You can read more about how to use it in `minimizer/README.md`.
The minimizer can be used in combination with fuzzing, bug replication and of course
bug reporting.

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
- [C11 Standard final draft](http://port70.net/~nsz/c/c11/n1570.html)
- [C99 Standard final draft](http://port70.net/~nsz/c/c99/n1256.html)
- [C89 Standard final draft](http://port70.net/~nsz/c/c89/c89-draft.html)
- [Yacc grammar for C11](http://www.quut.com/c/ANSI-C-grammar-y.html)
- [Lex grammar for C11](http://www.quut.com/c/ANSI-C-grammar-l-2011.html)
- [8cc](https://github.com/rui314/8cc), a self-hosting C compiler
- [tcc](https://github.com/LuaDist/tcc), a self-hosting C compiler originally [written for IOCCC](https://bellard.org/otcc/)

### Documentation for codegen

- [cranelift_frontend::FunctionBuilder](https://docs.rs/cranelift-frontend/0.43.0/cranelift_frontend/struct.FunctionBuilder.html)
- [cranelift_codegen::InstBuilder](https://docs.rs/cranelift-codegen/0.43.0/cranelift_codegen/ir/trait.InstBuilder.html)
- [cranelift_module::Module](https://docs.rs/cranelift-module/0.43.0/cranelift_module/struct.Module.html)

## Code of Conduct

There is not currently a code of conduct. Please do not do anything that would require me to make one.
