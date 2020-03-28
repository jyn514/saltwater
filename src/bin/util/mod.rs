use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, Read, Write};
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
    data::{
        error::{CompileWarning, RecoverableResult},
        lex::Location,
    },
    Error, Files, Opt,
};
use std::ffi::OsStr;

static ERRORS: AtomicUsize = AtomicUsize::new(0);
static WARNINGS: AtomicUsize = AtomicUsize::new(0);

pub struct BinOpt {
    /// The options that will be passed to `compile()`
    pub opt: Opt,
    /// If set, preprocess only, but do not do anything else.
    ///
    /// Note that preprocessing discards whitespace and comments.
    /// There is not currently a way to disable this behavior.
    pub preprocess_only: bool,
    /// The file to read C source from. \"-\" means stdin (use ./- to read a file called '-').
    /// Only one file at a time is currently accepted. [default: -]
    pub filename: PathBuf,
}

pub fn preprocess<W: Write>(
    buf: &str,
    opt: &Opt,
    file_id: FileId,
    file_db: &mut Files,
    mut out_buf: W,
) -> Result<(), Error> {
    let (tokens, warnings) = rcc::preprocess(&buf, &opt, file_id, file_db);
    handle_warnings(warnings, file_db);

    //let stdout = io::stdout();
    //let mut stdout_buf = BufWriter::new(stdout.lock());
    for token in tokens.map_err(Error::Source)? {
        write!(out_buf, "{} ", token.data).expect("failed to write to stdout");
    }
    writeln!(out_buf).expect("failed to write to stdout");

    Ok(())
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

pub fn impl_main<F>(real_main: F, usage: &str, help: &str)
where
    F: Fn(Rc<str>, &mut Files, FileId, &BinOpt, Option<&Path>) -> Result<(), Error>,
{
    #[cfg(debug_assertions)]
    color_backtrace::install();

    let (mut opt, output) = match parse_args(help) {
        Ok(opt) => opt,
        Err(err) => {
            println!(
                "{}: error parsing args: {}",
                std::env::args()
                    .next()
                    .unwrap_or_else(|| env!("CARGO_PKG_NAME").into()),
                err
            );
            println!("{}", usage);
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
    real_main(buf, &mut file_db, file_id, &opt, output.as_deref())
        .unwrap_or_else(|err| err_exit(err, opt.opt.max_errors, &file_db));
}

fn os_str_to_path_buf(os_str: &OsStr) -> Result<PathBuf, bool> {
    Ok(os_str.into())
}

macro_rules! type_sizes {
    ($($type: ty),*) => {
        $(println!("{}: {}", stringify!($type), std::mem::size_of::<$type>());)*
    };
}
fn parse_args(help: &str) -> Result<(BinOpt, Option<PathBuf>), pico_args::Error> {
    let mut input = Arguments::from_env();
    if input.contains(["-h", "--help"]) {
        println!("{}", help);
        std::process::exit(1);
    }
    if input.contains(["-V", "--version"]) {
        println!("{} {}", env!("CARGO_PKG_NAME"), env!("RCC_GIT_REV"));
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
    let output = input.opt_value_from_os_str(["-o", "--output"], os_str_to_path_buf)?;
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
        .location(file, location.span.start())
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

fn fatal<T: std::fmt::Display>(msg: T, code: i32) -> ! {
    eprintln!("{}: {}", Colour::Black.bold().paint("fatal"), msg);
    process::exit(code);
}

#[cfg(test)]
mod test {
    use super::{Files, Location};
    use ansi_term::Style;
    use codespan::Span;

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
