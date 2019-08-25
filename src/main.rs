use std::fs::File;
use std::io::{self, Read};
use std::path::PathBuf;
use std::process;

extern crate structopt;
use structopt::StructOpt;

extern crate compiler;
use compiler::{assemble, compile, link, utils, CompileError};
use tempfile::NamedTempFile;

#[derive(StructOpt, Debug)]
#[structopt(rename_all = "kebab")]
pub struct Opt {
    /// The file to read C source from.
    /// "-" means stdin (use ./- to read a file called '-').
    /// Only one file at a time is currently accepted.
    #[structopt(name = "FILE", default_value = "-", parse(from_os_str))]
    filename: PathBuf,

    /// If set, print all tokens found by the lexer in addition to compiling.
    #[structopt(long)]
    pub debug_lex: bool,

    /// If set, print the parsed abstract syntax tree in addition to compiling
    #[structopt(short = "a", long)]
    pub debug_ast: bool,

    /// If set, print the intermediate representation of the program in addition to compiling
    #[structopt(long)]
    pub debug_asm: bool,

    /// If set, compile and assemble but do not link. Object file is machine-dependent.
    #[structopt(short = "c", long)]
    pub no_link: bool,

    /// The output file to use.
    #[structopt(short = "o", long, default_value = "a.out", parse(from_os_str))]
    pub output: PathBuf,
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
// TODO: then we can move this into `main` and have main return `Result<(), CompileError>`
fn real_main(buf: String, opt: Opt) -> Result<(), CompileError> {
    let product = compile(
        buf,
        opt.filename.to_string_lossy().into_owned(),
        opt.debug_lex,
        opt.debug_ast,
        opt.debug_asm,
    )?;
    if opt.no_link {
        return assemble(product, opt.output.as_path());
    }
    let tmp_file = NamedTempFile::new()?;
    assemble(product, tmp_file.as_ref())?;
    link(tmp_file.as_ref(), opt.output.as_path()).map_err(io::Error::into)
}

fn main() {
    let mut opt = Opt::from_args();
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
    real_main(buf, opt).unwrap_or_else(|err| err_exit(err));
}

fn err_exit(err: CompileError) -> ! {
    use CompileError::*;
    match err {
        Semantic(err) => {
            utils::error(&err.data, &err.location);
            let (num_warnings, num_errors) = (utils::get_warnings(), utils::get_errors());
            print_issues(num_warnings, num_errors);
            process::exit(2);
        }
        IO(err) => utils::fatal(&format!("{}", err), 3),
        Platform(err) => utils::fatal(&format!("{}", err), 4),
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
