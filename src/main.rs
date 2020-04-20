use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, Read};
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[cfg(debug_assertions)]
use color_backtrace::termcolor;

use ansi_term::{ANSIString, Colour};
use codespan::FileId;
use git_testament::git_testament_macros;
use pico_args::Arguments;
use rcc::{
    assemble, compile,
    data::{error::CompileWarning, Location},
    link, preprocess, Error, Files, Opt,
};
use std::ffi::OsStr;
use tempfile::NamedTempFile;

static ERRORS: AtomicUsize = AtomicUsize::new(0);
static WARNINGS: AtomicUsize = AtomicUsize::new(0);

git_testament_macros!(version);

const HELP: &str = concat!(
    env!("CARGO_PKG_NAME"), " ", version_testament!(), "\n",
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
        --color <when>       When to use color. May be \"never\", \"auto\", or \"always\". [default: auto]
    -o, --output <output>    The output file to use. [default: a.out]
        --max-errors <max>   The maximum number of errors to allow before giving up.
                             Use 0 to allow unlimited errors. [default: 10]
    -I, --include <dir>      Add a directory to the local include path (`#include \"file.h\"`).
                              Can be specified multiple times to add multiple directories.
    -D, --define <id[=val]>  Define an object-like macro.
                              Can be specified multiple times to add multiple macros.
                              `val` defaults to `1`.

ARGS:
    <file>    The file to read C source from. \"-\" means stdin (use ./- to read a file called '-').
              Only one file at a time is currently accepted. [default: -]"
);

const USAGE: &str = "\
usage: rcc [--help] [--version | -V] [--debug-asm] [--debug-ast | -a]
           [--debug-lex] [--jit] [--no-link | -c] [-I <dir>] [-D <id[=val]>] [<file>]";

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
    /// Whether or not to use color
    color: ColorChoice,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ColorChoice {
    Always,
    Auto,
    Never,
}

impl ColorChoice {
    fn use_color_for(self, stream: atty::Stream) -> bool {
        match self {
            ColorChoice::Always => true,
            ColorChoice::Never => false,
            ColorChoice::Auto => atty::is(stream),
        }
    }
}

impl std::str::FromStr for ColorChoice {
    type Err = &'static str;
    fn from_str(s: &str) -> Result<ColorChoice, &'static str> {
        match s {
            "always" => Ok(ColorChoice::Always),
            "auto" => Ok(ColorChoice::Auto),
            "never" => Ok(ColorChoice::Never),
            _ => Err("Invalid color choice"),
        }
    }
}

impl Into<termcolor::ColorChoice> for ColorChoice {
    fn into(self) -> termcolor::ColorChoice {
        match self {
            ColorChoice::Always => termcolor::ColorChoice::Always,
            ColorChoice::Auto => termcolor::ColorChoice::Auto,
            ColorChoice::Never => termcolor::ColorChoice::Never,
        }
    }
}

// TODO: when std::process::termination is stable, make err_exit an impl for CompileError
// TODO: then we can move this into `main` and have main return `Result<(), Error>`
fn real_main(
    buf: Rc<str>,
    file_db: &mut Files,
    file_id: FileId,
    bin_opt: BinOpt,
    output: &Path,
) -> Result<(), Error> {
    let opt = if bin_opt.preprocess_only {
        use std::io::{BufWriter, Write};

        let (tokens, warnings) = preprocess(&buf, bin_opt.opt, file_id, file_db);
        handle_warnings(warnings, file_db, bin_opt.color);

        let stdout = io::stdout();
        let mut stdout_buf = BufWriter::new(stdout.lock());
        for token in tokens.map_err(Error::Source)? {
            write!(stdout_buf, "{} ", token.data).expect("failed to write to stdout");
        }
        writeln!(stdout_buf).expect("failed to write to stdout");

        return Ok(());
    } else {
        bin_opt.opt
    };
    #[cfg(feature = "jit")]
    {
        if !opt.jit {
            aot_main(&buf, opt, file_id, file_db, output, bin_opt.color)
        } else {
            let module = rcc::initialize_jit_module();
            let (result, warnings) = compile(module, &buf, opt, file_id, file_db);
            handle_warnings(warnings, file_db, bin_opt.color);
            let mut rccjit = rcc::JIT::from(result?);
            if let Some(exit_code) = unsafe { rccjit.run_main() } {
                std::process::exit(exit_code);
            }
            Ok(())
        }
    }
    #[cfg(not(feature = "jit"))]
    aot_main(&buf, opt, file_id, file_db, output, bin_opt.color)
}

#[inline]
fn aot_main(
    buf: &str,
    opt: Opt,
    file_id: FileId,
    file_db: &mut Files,
    output: &Path,
    color: ColorChoice,
) -> Result<(), Error> {
    let no_link = opt.no_link;
    let module = rcc::initialize_aot_module("rccmain".to_owned());
    let (result, warnings) = compile(module, buf, opt, file_id, file_db);
    handle_warnings(warnings, file_db, color);

    let product = result.map(|x| x.finish())?;
    if no_link {
        return assemble(product, output);
    }
    let tmp_file = NamedTempFile::new()?;
    assemble(product, tmp_file.as_ref())?;
    link(tmp_file.as_ref(), output).map_err(io::Error::into)
}

fn handle_warnings(warnings: VecDeque<CompileWarning>, file_db: &Files, color: ColorChoice) {
    WARNINGS.fetch_add(warnings.len(), Ordering::Relaxed);
    let tag = if color.use_color_for(atty::Stream::Stdout) {
        Colour::Yellow.bold().paint("warning")
    } else {
        ANSIString::from("warning")
    };
    for warning in warnings {
        print!(
            "{}",
            pretty_print(tag.clone(), warning.data, warning.location, file_db)
        );
    }
}

fn main() {
    #[cfg(debug_assertions)]
    use color_backtrace::{termcolor::StandardStream, BacktracePrinter};

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

    #[cfg(debug_assertions)]
    BacktracePrinter::new().install(Box::new(StandardStream::stderr(opt.color.into())));

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
    let max_errors = opt.opt.max_errors;
    let color_choice = opt.color;
    real_main(buf, &mut file_db, file_id, opt, &output)
        .unwrap_or_else(|err| err_exit(err, max_errors, &file_db, color_choice));
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
    use std::collections::HashMap;

    let mut input = Arguments::from_env();
    if input.contains(["-h", "--help"]) {
        println!("{}", HELP);
        std::process::exit(1);
    }
    if input.contains(["-V", "--version"]) {
        println!("{} {}", env!("CARGO_PKG_NAME"), version_testament!());
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
            hir::Variable,
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
    let color_choice = input
        .opt_value_from_str("--color")?
        .unwrap_or(ColorChoice::Auto);
    let mut search_path = Vec::new();
    while let Some(include) =
        input.opt_value_from_os_str(["-I", "--include"], os_str_to_path_buf)?
    {
        search_path.push(include);
    }
    let mut definitions = HashMap::new();
    while let Some(arg) = input.opt_value_from_str::<_, String>(["-D", "--define"])? {
        use std::convert::TryInto;

        let mut iter = arg.splitn(2, '=');
        let key = iter
            .next()
            .expect("apparently I don't understand pico_args");
        let val = iter.next().unwrap_or("1");
        let def = val.try_into().map_err(|err: rcc::data::error::LexError| {
            pico_args::Error::ArgumentParsingFailed {
                cause: err.to_string(),
            }
        })?;
        definitions.insert(key.into(), def);
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
                definitions,
                search_path,
            },
            filename: input
                .free_from_os_str(os_str_to_path_buf)?
                .unwrap_or_else(|| "-".into()),
            color: color_choice,
        },
        output,
    ))
}

fn err_exit(
    err: Error,
    max_errors: Option<NonZeroUsize>,
    file_db: &Files,
    color: ColorChoice,
) -> ! {
    use Error::*;
    match err {
        Source(errs) => {
            for err in &errs {
                error(&err.data, err.location(), file_db, color);
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
        IO(err) => fatal(&err, 3, color),
        Platform(err) => fatal(&err, 4, color),
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

fn error<T: std::fmt::Display>(msg: T, location: Location, file_db: &Files, color: ColorChoice) {
    ERRORS.fetch_add(1, Ordering::Relaxed);
    let prefix = if color.use_color_for(atty::Stream::Stdout) {
        Colour::Red.bold().paint("error")
    } else {
        ANSIString::from("error")
    };
    print!("{}", pretty_print(prefix, msg, location, file_db,));
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

fn fatal<T: std::fmt::Display>(msg: T, code: i32, color: ColorChoice) -> ! {
    if color.use_color_for(atty::Stream::Stderr) {
        eprintln!("{}: {}", Colour::Black.bold().paint("fatal"), msg);
    } else {
        eprintln!("fatal: {}", msg);
    }
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
