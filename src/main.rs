use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, Read};
use std::path::PathBuf;
use std::process;
use std::sync::atomic::{AtomicUsize, Ordering};

extern crate ansi_term;
extern crate env_logger;
extern crate log;
extern crate pico_args;
extern crate rcc;

use ansi_term::{ANSIString, Colour};
use pico_args::Arguments;
use rcc::{
    assemble, compile,
    data::{
        error::{CompileWarning, RecoverableResult},
        lex::Location,
    },
    intern::STRINGS,
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
fn real_main(buf: &str, opt: Opt) -> Result<(), Error> {
    env_logger::init();
    let (result, warnings) = compile(
        buf,
        opt.filename.to_string_lossy().into_owned(),
        opt.debug_lex,
        opt.debug_ast,
        opt.debug_asm,
    );
    handle_warnings(warnings, buf);

    let product = result?;
    if opt.no_link {
        return assemble(product, opt.output.as_path());
    }
    let tmp_file = NamedTempFile::new()?;
    assemble(product, tmp_file.as_ref())?;
    link(tmp_file.as_ref(), opt.output.as_path()).map_err(io::Error::into)
}

fn handle_warnings(warnings: VecDeque<CompileWarning>, file: &str) {
    WARNINGS.fetch_add(warnings.len(), Ordering::Relaxed);
    let tag = Colour::Yellow.bold().paint("warning");
    for warning in warnings {
        pretty_print(tag.clone(), warning.data, warning.location, file);
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
    // why a closure instead of err_exit?
    // from a conversation in discord#rust-usage:
    //
    // A ! value can be coerced into any type implicitly
    // When you take the function directly you have a value of fn(&'static str) -> ! and that can't be coerced
    // When you call it you get a value of ! which can
    // It's like &String can be coerced to &str, but it's not a subtype of it
    // Likewise a fn(T) -> &String should not be allowed to coerce to fn(T) -> &str
    //
    // What's happening here is the function has type `fn(...) -> !`,
    // but when it's called, that's coerced to `!`,
    // so the closure has type `fn(...) -> i32`
    real_main(&buf, opt).unwrap_or_else(|err| err_exit(err, &buf));
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

fn err_exit(err: Error, file: &str) -> ! {
    use Error::*;
    match err {
        Source(errs) => {
            for err in errs {
                error(&err.data, err.location(), file);
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

fn error<T: std::fmt::Display>(msg: T, location: Location, file: &str) {
    ERRORS.fetch_add(1, Ordering::Relaxed);
    pretty_print(Colour::Red.bold().paint("error"), msg, location, file);
}

pub fn pretty_print<T: std::fmt::Display>(
    prefix: ANSIString,
    msg: T,
    location: Location,
    file: &str,
) {
    let (line, column) = location.calculate_line_column(file);
    println!(
        "{}:{}:{}: {}: {}",
        STRINGS
            .read()
            .unwrap()
            .resolve(location.filename.0)
            .unwrap(),
        line,
        column,
        prefix,
        msg
    );
}

#[inline]
fn get_warnings() -> usize {
    ERRORS.load(Ordering::SeqCst)
}

#[inline]
fn get_errors() -> usize {
    ERRORS.load(Ordering::SeqCst)
}
