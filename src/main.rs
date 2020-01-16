use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, Read};
use std::path::PathBuf;
use std::process;
use std::sync::atomic::{AtomicUsize, Ordering};

extern crate ansi_term;
extern crate codespan;
extern crate env_logger;
extern crate log;
extern crate pico_args;
extern crate rcc;

use ansi_term::{ANSIString, Colour};
use codespan::{FileId, Files};
use pico_args::Arguments;
use rcc::{
    assemble, compile,
    data::{
        error::{CompileWarning, RecoverableResult},
        lex::Location,
    },
    link, utils, Error,
};
use std::ffi::OsStr;
use tempfile::NamedTempFile;

static ERRORS: AtomicUsize = AtomicUsize::new(0);
static WARNINGS: AtomicUsize = AtomicUsize::new(0);

const HELP: &str = concat!(
    env!("CARGO_PKG_NAME"), " ", env!("CARGO_PKG_VERSION"), "\n",
    env!("CARGO_PKG_AUTHORS"), "\n",
    env!("CARGO_PKG_DESCRIPTION"), "\n",
    "Homepage: ", env!("CARGO_PKG_REPOSITORY"), "\n",
    "\n",
"usage: ", env!("CARGO_PKG_NAME"), " [FLAGS] [OPTIONS] [<file>]

FLAGS:
        --debug-asm    If set, print the intermediate representation of the program in addition to compiling
    -a, --debug-ast    If set, print the parsed abstract syntax tree in addition to compiling
        --debug-lex    If set, print all tokens found by the lexer in addition to compiling.
    -h, --help         Prints help information
    -c, --no-link      If set, compile and assemble but do not link. Object file is machine-dependent.
    -V, --version      Prints version information

OPTIONS:
    -o, --output <output>    The output file to use. [default: a.out]

ARGS:
    <file>    The file to read C source from. \"-\" means stdin (use ./- to read a file called '-').
              Only one file at a time is currently accepted. [default: -]");

const USAGE: &str = "\
usage: rcc [--help] [--version | -V] [--debug-asm] [--debug-ast | -a]
           [--debug-lex] [--no-link | -c] [<file>]";

#[derive(Debug)]
struct Opt {
    /// The file to read C source from.
    /// "-" means stdin (use ./- to read a file called '-').
    /// Only one file at a time is currently accepted.
    filename: PathBuf,

    /// If set, print all tokens found by the lexer in addition to compiling.
    debug_lex: bool,

    /// If set, print the parsed abstract syntax tree in addition to compiling
    debug_ast: bool,

    /// If set, print the intermediate representation of the program in addition to compiling
    debug_asm: bool,

    /// If set, compile and assemble but do not link. Object file is machine-dependent.
    no_link: bool,

    /// The output file to use.
    output: PathBuf,
}

impl Default for Opt {
    fn default() -> Self {
        Opt {
            filename: "<default>".into(),
            debug_lex: false,
            debug_ast: false,
            debug_asm: false,
            no_link: false,
            output: PathBuf::from("a.out"),
        }
    }
}

// TODO: when std::process::termination is stable, make err_exit an impl for CompilerError
// TODO: then we can move this into `main` and have main return `Result<(), Error>`
fn real_main(file_db: &Files<String>, file_id: FileId, opt: Opt) -> Result<(), Error> {
    env_logger::init();
    let (result, warnings) = compile(
        file_db.source(file_id),
        opt.filename.to_string_lossy().into_owned(),
        opt.debug_lex,
        opt.debug_ast,
        opt.debug_asm,
    );
    handle_warnings(warnings, file_id, file_db);

    let product = result?;
    if opt.no_link {
        return assemble(product, opt.output.as_path());
    }
    let tmp_file = NamedTempFile::new()?;
    assemble(product, tmp_file.as_ref())?;
    link(tmp_file.as_ref(), opt.output.as_path()).map_err(io::Error::into)
}

fn handle_warnings(warnings: VecDeque<CompileWarning>, file: FileId, file_db: &Files<String>) {
    WARNINGS.fetch_add(warnings.len(), Ordering::Relaxed);
    let tag = Colour::Yellow.bold().paint("warning");
    for warning in warnings {
        print!(
            "{}",
            pretty_print(tag.clone(), warning.data, warning.location, file, file_db)
        );
    }
}

fn main() {
    let mut opt = match parse_args() {
        Ok(opt) => opt,
        Err(err) => {
            println!(
                "{}: error parsing args: {}",
                std::env::args()
                    .next()
                    .unwrap_or_else(|| env!("CARGO_PKG_NAME").into()),
                err
            );
            println!("{}", USAGE);
            std::process::exit(1);
        }
    };
    // NOTE: only holds valid UTF-8; will panic otherwise
    let mut buf = String::new();
    opt.filename = if opt.filename == PathBuf::from("-") {
        io::stdin().read_to_string(&mut buf).unwrap_or_else(|err| {
            eprintln!("Failed to read stdin: {}", err);
            process::exit(1);
        });
        PathBuf::from("<stdin>")
    } else {
        File::open(opt.filename.as_path())
            .and_then(|mut file| file.read_to_string(&mut buf))
            .unwrap_or_else(|err| {
                eprintln!("Failed to read {}: {}", opt.filename.to_string_lossy(), err);
                process::exit(1);
            });
        opt.filename
    };

    let mut file_db = Files::new();
    // TODO: remove `lossy` call
    let file_id = file_db.add(&opt.filename, buf);
    real_main(&file_db, file_id, opt).unwrap_or_else(|err| err_exit(err, file_id, &file_db));
}

fn os_str_to_path_buf(os_str: &OsStr) -> Result<PathBuf, bool> {
    Ok(os_str.into())
}

macro_rules! type_sizes {
    ($($type: ty),*) => {
        $(println!("{}: {}", stringify!($type), std::mem::size_of::<$type>());)*
    };
}
fn parse_args() -> Result<Opt, pico_args::Error> {
    let mut input = Arguments::from_env();
    if input.contains(["-h", "--help"]) {
        println!("{}", HELP);
        std::process::exit(1);
    }
    if input.contains(["-V", "--version"]) {
        println!("{} {}", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"));
        std::process::exit(0);
    }
    if input.contains("--print-type-sizes") {
        use rcc::data::prelude::*;
        type_sizes!(
            Location,
            CompileError,
            Type,
            Expr,
            ExprType,
            Stmt,
            StmtType,
            Declaration,
            Symbol,
            StructType,
            Token,
            RecoverableResult<Expr>
        );
    }
    Ok(Opt {
        debug_lex: input.contains("--debug-lex"),
        debug_asm: input.contains("--debug-asm"),
        debug_ast: input.contains(["-a", "--debug-ast"]),
        no_link: input.contains(["-c", "--no-link"]),
        output: input
            .opt_value_from_os_str(["-o", "--output"], os_str_to_path_buf)?
            .unwrap_or_else(|| "a.out".into()),
        filename: input
            .free_from_os_str(os_str_to_path_buf)?
            .unwrap_or_else(|| "-".into()),
    })
}

fn err_exit(err: Error, file: FileId, file_db: &Files<String>) -> ! {
    use Error::*;
    match err {
        Source(errs) => {
            for err in errs {
                error(&err.data, err.location(), file, file_db);
            }
            let (num_warnings, num_errors) = (get_warnings(), get_errors());
            print_issues(num_warnings, num_errors);
            process::exit(2);
        }
        IO(err) => utils::fatal(&err, 3),
        Platform(err) => utils::fatal(&err, 4),
    }
}

fn print_issues(warnings: usize, errors: usize) {
    if warnings == 0 && errors == 0 {
        return;
    }
    let warn_msg = if warnings > 1 { "warnings" } else { "warning" };
    let err_msg = if errors > 1 { "errors" } else { "error" };
    let msg = match (warnings, errors) {
        (0, _) => format!("{} {}", errors, err_msg),
        (_, 0) => format!("{} {}", warnings, warn_msg),
        (_, _) => format!("{} {} and {} {}", warnings, warn_msg, errors, err_msg),
    };
    eprintln!("{} generated", msg);
}

fn error<T: std::fmt::Display>(msg: T, location: Location, file: FileId, file_db: &Files<String>) {
    ERRORS.fetch_add(1, Ordering::Relaxed);
    print!(
        "{}",
        pretty_print(
            Colour::Red.bold().paint("error"),
            msg,
            location,
            file,
            file_db,
        )
    );
}

#[must_use]
pub fn pretty_print<T: std::fmt::Display, S: AsRef<str>>(
    prefix: ANSIString,
    msg: T,
    location: Location,
    file: FileId,
    file_db: &Files<S>,
) -> String {
    let start = file_db
        .location(file, location.span.start())
        .expect("start location should be in bounds");
    let buf = format!(
        "{}:{}:{}: {}: {}\n",
        PathBuf::from(file_db.name(file)).display(),
        start.line.number(),
        start.column.number(),
        prefix,
        msg
    );
    // avoid printing spurious newline for errors and EOF
    if location.span.end() == 0.into() {
        return buf;
    }
    let end = file_db
        .location(file, location.span.end())
        .expect("end location should be in bounds");
    if start.line == end.line {
        let line = file_db
            .line_span(file, start.line)
            .expect("line should be in bounds");
        format!(
            "{}{}{}{}\n",
            buf,
            file_db.source_slice(file, line).unwrap(),
            " ".repeat(start.column.0 as usize),
            "^".repeat((end.column - start.column).0 as usize)
        )
    } else {
        buf
    }
}

#[inline]
fn get_warnings() -> usize {
    ERRORS.load(Ordering::SeqCst)
}

#[inline]
fn get_errors() -> usize {
    ERRORS.load(Ordering::SeqCst)
}

#[cfg(test)]
mod test {
    use super::{Files, Location};
    use ansi_term::Style;
    use codespan::Span;
    use rcc::intern::InternedStr;

    fn pp<S: Into<Span>>(span: S, source: &str) -> String {
        let location = Location {
            filename: InternedStr::get_or_intern("<test-suite>"),
            span: span.into(),
        };
        let mut file_db = Files::new();
        let file = file_db.add("<test-suite>", source);
        let ansi_str = Style::new().paint("");
        super::pretty_print(ansi_str, "", location, file, &file_db)
    }
    #[test]
    fn pretty_print() {
        assert_eq!(
            dbg!(pp(8..15, "int i = \"hello\";\n")).lines().nth(2),
            Some("        ^^^^^^^")
        );
        pp(0..0, "");
    }
}
