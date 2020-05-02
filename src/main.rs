use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, Read};
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

extern crate ansi_term;
extern crate codespan;
#[cfg(debug_assertions)]
extern crate color_backtrace;
extern crate pico_args;
extern crate rcc;

use ansi_term::{ANSIString, Colour};
use codespan::FileId;
use pico_args::Arguments;
use rcc::{
    assemble, compile,
    data::{error::CompileWarning, Location},
    link, preprocess, Error, Files, Opt,
};
use std::ffi::OsStr;
use target_lexicon::Triple;
use tempfile::NamedTempFile;

static ERRORS: AtomicUsize = AtomicUsize::new(0);
static WARNINGS: AtomicUsize = AtomicUsize::new(0);

const HELP: &str = concat!(
    env!("CARGO_PKG_NAME"), " ", env!("RCC_GIT_REV"), "\n",
    "Joshua Nelson <jyn514@gmail.com>\n",
    env!("CARGO_PKG_DESCRIPTION"), "\n",
    "Homepage: ", env!("CARGO_PKG_REPOSITORY"), "\n",
    "\n",
"usage: ", env!("CARGO_PKG_NAME"), " [FLAGS] [OPTIONS] [<file>]

FLAGS:
        --debug-asm        If set, print the intermediate representation of the program in addition to compiling
    -a, --debug-ast        If set, print the parsed abstract syntax tree in addition to compiling
        --debug-lex        If set, print all tokens found by the lexer in addition to compiling.
        --jit              If set, will use JIT compilation for C code and instantly run compiled code (No files produced).
                           NOTE: this option only works if rcc was compiled with the `jit` feature.
    -h, --help             Prints help information
    -c, --no-link          If set, compile and assemble but do not link. Object file is machine-dependent.
    -E, --preprocess-only  If set, preprocess only, but do not do anything else.
                            Note that preprocessing discards whitespace and comments.
                            There is not currently a way to disable this behavior.
    -V, --version          Prints version information
    

OPTIONS:
    -o, --output <output>    The output file to use. [default: a.out]
        --max-errors <max>   The maximum number of errors to allow before giving up.
                             Use 0 to allow unlimited errors. [default: 10]
    -I, --include <dir>      Add a directory to the local include path (`#include \"file.h\"`)
        --target  <target>   The target platform to compile to. Allows cross-compilation.

ARGS:
    <file>    The file to read C source from. \"-\" means stdin (use ./- to read a file called '-').
              Only one file at a time is currently accepted. [default: -]");

const USAGE: &str = "\
usage: rcc [--help] [--version | -V] [--debug-asm] [--debug-ast | -a]
           [--debug-lex] [--jit] [--no-link | -c] [-I <dir>] [<file>]";

struct BinOpt {
    /// The options that will be passed to `compile()`
    opt: Opt,
    /// If set, preprocess only, but do not do anything else.
    ///
    /// Note that preprocessing discards whitespace and comments.
    /// There is not currently a way to disable this behavior.
    preprocess_only: bool,
    /// The file to read C source from. \"-\" means stdin (use ./- to read a file called '-').
    /// Only one file at a time is currently accepted. [default: -]
    filename: PathBuf,
}

// TODO: when std::process::termination is stable, make err_exit an impl for CompilerError
// TODO: then we can move this into `main` and have main return `Result<(), Error>`
fn real_main(
    buf: Rc<str>,
    file_db: &mut Files,
    file_id: FileId,
    opt: &BinOpt,
    output: &Path,
) -> Result<(), Error> {
    let opt = if opt.preprocess_only {
        use std::io::{BufWriter, Write};

        let (tokens, warnings) = preprocess(&buf, &opt.opt, file_id, file_db);
        handle_warnings(warnings, file_db);

        let stdout = io::stdout();
        let mut stdout_buf = BufWriter::new(stdout.lock());
        for token in tokens.map_err(Error::Source)? {
            write!(stdout_buf, "{} ", token.data).expect("failed to write to stdout");
        }
        writeln!(stdout_buf).expect("failed to write to stdout");

        return Ok(());
    } else {
        &opt.opt
    };
    #[cfg(feature = "jit")]
    {
        if !opt.jit {
            aot_main(&buf, &opt, file_id, file_db, output)
        } else {
            let module = rcc::initialize_jit_module();
            let (result, warnings) = compile(module, &buf, &opt, file_id, file_db);
            handle_warnings(warnings, file_db);
            let mut rccjit = rcc::JIT::from(result?);
            if let Some(exit_code) = unsafe { rccjit.run_main() } {
                std::process::exit(exit_code);
            }
            Ok(())
        }
    }
    #[cfg(not(feature = "jit"))]
    aot_main(&buf, &opt, file_id, file_db, output)
}

#[inline]
fn aot_main(
    buf: &str,
    opt: &Opt,
    file_id: FileId,
    file_db: &mut Files,
    output: &Path,
) -> Result<(), Error> {
    let module = rcc::initialize_aot_module("rccmain".to_owned(), opt.target.clone());
    let (result, warnings) = compile(module, buf, opt, file_id, file_db);
    handle_warnings(warnings, file_db);

    let product = result.map(|x| x.finish())?;
    if opt.no_link {
        return assemble(product, output);
    }
    let tmp_file = NamedTempFile::new()?;
    assemble(product, tmp_file.as_ref())?;
    link(tmp_file.as_ref(), output).map_err(io::Error::into)
}

fn handle_warnings(warnings: VecDeque<CompileWarning>, file_db: &Files) {
    WARNINGS.fetch_add(warnings.len(), Ordering::Relaxed);
    let tag = Colour::Yellow.bold().paint("warning");
    for warning in warnings {
        print!(
            "{}",
            pretty_print(tag.clone(), warning.data, warning.location, file_db)
        );
    }
}

fn main() {
    #[cfg(debug_assertions)]
    color_backtrace::install();

    let (mut opt, output) = match parse_args() {
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
    let buf: Rc<_> = buf.into();
    let source = rcc::Source {
        path: opt.filename.clone(),
        code: Rc::clone(&buf),
    };

    let mut file_db = Files::new();
    let file_id = file_db.add(&opt.filename, source);
    real_main(buf, &mut file_db, file_id, &opt, &output)
        .unwrap_or_else(|err| err_exit(err, opt.opt.max_errors, &file_db));
}

fn os_str_to_path_buf(os_str: &OsStr) -> Result<PathBuf, bool> {
    Ok(os_str.into())
}

macro_rules! type_sizes {
    ($($type: ty),* $(,)?) => {
        $(println!("{}: {}", stringify!($type), std::mem::size_of::<$type>());)*
    };
}
fn parse_args() -> Result<(BinOpt, PathBuf), pico_args::Error> {
    let mut input = Arguments::from_env();
    if input.contains(["-h", "--help"]) {
        println!("{}", HELP);
        std::process::exit(1);
    }
    if input.contains(["-V", "--version"]) {
        println!("{} {}", env!("CARGO_PKG_NAME"), env!("RCC_GIT_REV"));
        std::process::exit(0);
    }
    if input.contains("--print-type-sizes") {
        use rcc::data::*;
        type_sizes!(
            Location,
            CompileError,
            Type,
            ast::Expr,
            ast::ExprType,
            hir::Expr,
            hir::ExprType,
            ast::Stmt,
            ast::StmtType,
            hir::Stmt,
            hir::StmtType,
            ast::Declaration,
            hir::Declaration,
            hir::Metadata,
            StructType,
            Token,
        );
    }
    let output = input
        .opt_value_from_os_str(["-o", "--output"], os_str_to_path_buf)?
        .unwrap_or_else(|| "a.out".into());
    let max_errors = input
        .opt_value_from_fn("--max-errors", |s| {
            usize::from_str_radix(s, 10).map(NonZeroUsize::new)
        })?
        .unwrap_or_else(|| Some(NonZeroUsize::new(10).unwrap()));
    let mut search_path = Vec::new();
    while let Some(include) =
        input.opt_value_from_os_str(["-I", "--include"], os_str_to_path_buf)?
    {
        search_path.push(include);
    }
    Ok((
        BinOpt {
            preprocess_only: input.contains(["-E", "--preprocess-only"]),
            opt: Opt {
                debug_lex: input.contains("--debug-lex"),
                debug_asm: input.contains("--debug-asm"),
                debug_ast: input.contains(["-a", "--debug-ast"]),
                no_link: input.contains(["-c", "--no-link"]),
                target: dbg!(input
                    .opt_value_from_str("--target")?
                    .unwrap_or_else(Triple::host)),
                #[cfg(feature = "jit")]
                jit: input.contains("--jit"),
                max_errors,
                search_path,
            },
            filename: input
                .free_from_os_str(os_str_to_path_buf)?
                .unwrap_or_else(|| "-".into()),
        },
        output,
    ))
}

fn err_exit(err: Error, max_errors: Option<NonZeroUsize>, file_db: &Files) -> ! {
    use Error::*;
    match err {
        Source(errs) => {
            for err in &errs {
                error(&err.data, err.location(), file_db);
            }
            if let Some(max) = max_errors {
                if usize::from(max) <= errs.len() {
                    println!(
                        "fatal: too many errors (--max-errors {}), stopping now",
                        max
                    );
                }
            }
            let (num_warnings, num_errors) = (get_warnings(), get_errors());
            print_issues(num_warnings, num_errors);
            process::exit(2);
        }
        IO(err) => fatal(&err, 3),
        Platform(err) => fatal(&err, 4),
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

fn error<T: std::fmt::Display>(msg: T, location: Location, file_db: &Files) {
    ERRORS.fetch_add(1, Ordering::Relaxed);
    print!(
        "{}",
        pretty_print(Colour::Red.bold().paint("error"), msg, location, file_db,)
    );
}

#[must_use]
fn pretty_print<T: std::fmt::Display>(
    prefix: ANSIString,
    msg: T,
    location: Location,
    file_db: &Files,
) -> String {
    let file = location.file;
    let start = file_db
        .location(file, location.span.start)
        .expect("start location should be in bounds");
    let buf = format!(
        "{}:{}:{} {}: {}\n",
        file_db.name(file).to_string_lossy(),
        start.line.number(),
        start.column.number(),
        prefix,
        msg
    );
    // avoid printing spurious newline for errors and EOF
    if location.span.end == 0 {
        return buf;
    }
    let end = file_db
        .location(file, location.span.end)
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
    WARNINGS.load(Ordering::SeqCst)
}

#[inline]
fn get_errors() -> usize {
    ERRORS.load(Ordering::SeqCst)
}

fn fatal<T: std::fmt::Display>(msg: T, code: i32) -> ! {
    eprintln!("{}: {}", Colour::Black.bold().paint("fatal"), msg);
    process::exit(code);
}

#[cfg(test)]
mod test {
    use super::{Files, Location};
    use ansi_term::Style;
    //use codespan::Span;
    use rcc::data::lex::Span;

    fn pp<S: Into<Span>>(span: S, source: &str) -> String {
        let mut file_db = Files::new();
        let source = String::from(source).into();
        let file = file_db.add("<test-suite>", source);
        let location = Location {
            file,
            span: span.into(),
        };
        let ansi_str = Style::new().paint("");
        super::pretty_print(ansi_str, "", location, &file_db)
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
