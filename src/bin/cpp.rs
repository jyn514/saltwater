mod util;

const HELP: &str = concat!(
    env!("CARGO_PKG_NAME"),
    " ",
    env!("RCC_GIT_REV"),
    "\n",
    "Joshua Nelson <jyn514@gmail.com>\n",
    env!("CARGO_PKG_DESCRIPTION"),
    "\n",
    "Homepage: ",
    env!("CARGO_PKG_REPOSITORY"),
    "\n",
    "\n",
    "usage: ",
    env!("CARGO_PKG_NAME"),
    " [FLAGS] [OPTIONS] [<file>]

FLAGS:
        --debug-lex        If set, print all tokens found by the lexer in addition to compiling.
    -h, --help             Prints help information
    -E, --preprocess-only  If set, preprocess only, but do not do anything else.
                            Note that preprocessing discards whitespace and comments.
                            There is not currently a way to disable this behavior.
    -V, --version          Prints version information
    

OPTIONS:
    -o, --output <output>    The output file to use. [default: a.out]
        --max-errors <max>   The maximum number of errors to allow before giving up.
                             Use 0 to allow unlimited errors. [default: 10]
    -I, --include <dir>      Add a directory to the local include path (`#include \"file.h\"`)

ARGS:
    <file>    The file to read C source from. \"-\" means stdin (use ./- to read a file called '-').
              Only one file at a time is currently accepted. [default: -]"
);

const USAGE: &str = "usage: rcc [--help] [--version | -V] [--debug-lex] [-I <dir>] [<file>]";

fn main() {
    use std::fs::File;
    use std::io::{self, BufWriter};
    use std::path::Path;
    use std::rc::Rc;
    use util::{impl_main as main, preprocess, BinOpt};

    let real_main = |buf: Rc<str>, files: &mut _, file, opt: &BinOpt, output: Option<&Path>| {
        if let Some(path) = output {
            let out = BufWriter::new(File::open(path)?);
            preprocess(&buf, &opt.opt, file, files, out)
        } else {
            let stdout = io::stdout();
            let out = BufWriter::new(stdout.lock());
            preprocess(&buf, &opt.opt, file, files, out)
        }
    };
    main(real_main, USAGE, HELP);
}
