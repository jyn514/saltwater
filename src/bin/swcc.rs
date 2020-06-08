mod common;

use std::fs::File;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process;
use std::rc::Rc;

use common::{backtrace, err_exit, handle_warnings, parse_args, BinOpt, ColorChoice, USAGE};
use saltwater::{assemble, compile, link, preprocess, Error, Files, Opt, Program};
use tempfile::NamedTempFile;

macro_rules! sw_try {
    ($res: expr, $files: expr) => {
        match $res {
            Ok(program) => program,
            Err(err) => return Err((err.into(), $files)),
        }
    };
}

// TODO: when std::process::termination is stable, make err_exit an impl for CompileError
// TODO: then we can move this into `main` and have main return `Result<(), Error>`
fn real_main(buf: Rc<str>, bin_opt: BinOpt, output: &Path) -> Result<(), (Error, Files)> {
    let opt = if bin_opt.preprocess_only {
        use std::io::{BufWriter, Write};

        let Program {
            result: tokens,
            warnings,
            files,
        } = preprocess(&buf, bin_opt.opt);
        handle_warnings(warnings, &files, bin_opt.color);

        let stdout = io::stdout();
        let mut stdout_buf = BufWriter::new(stdout.lock());
        for token in sw_try!(tokens, files) {
            write!(stdout_buf, "{}", token.data).expect("failed to write to stdout");
        }

        return Ok(());
    } else {
        bin_opt.opt
    };
    #[cfg(feature = "jit")]
    {
        if !opt.jit {
            aot_main(&buf, opt, output, bin_opt.color)
        } else {
            let module = saltwater::initialize_jit_module();
            let Program {
                result,
                warnings,
                files,
            } = compile(module, &buf, opt);
            handle_warnings(warnings, &files, bin_opt.color);
            let mut jit = saltwater::JIT::from(sw_try!(result, files));
            if let Some(exit_code) = unsafe { jit.run_main() } {
                std::process::exit(exit_code);
            }
            Ok(())
        }
    }
    #[cfg(not(feature = "jit"))]
    aot_main(&buf, opt, output, bin_opt.color)
}

#[inline]
fn aot_main(buf: &str, opt: Opt, output: &Path, color: ColorChoice) -> Result<(), (Error, Files)> {
    let no_link = opt.no_link;
    let module = saltwater::initialize_aot_module("saltwater_main".to_owned());
    let Program {
        result,
        warnings,
        files,
    } = compile(module, buf, opt);
    handle_warnings(warnings, &files, color);

    let product = sw_try!(result.map(|x| x.finish()), files);
    if no_link {
        sw_try!(assemble(product, output), files);
        return Ok(());
    }
    let tmp_file = sw_try!(NamedTempFile::new(), files);
    sw_try!(assemble(product, tmp_file.as_ref()), files);
    sw_try!(link(tmp_file.as_ref(), output), files);
    Ok(())
}

fn main() {
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

    #[cfg(feature = "color-backtrace")]
    backtrace::install(opt.color);

    // NOTE: only holds valid UTF-8; will panic otherwise
    let mut buf = String::new();
    opt.opt.filename = if opt.opt.filename == PathBuf::from("-") {
        io::stdin().read_to_string(&mut buf).unwrap_or_else(|err| {
            eprintln!("Failed to read stdin: {}", err);
            process::exit(1);
        });
        PathBuf::from("<stdin>")
    } else {
        File::open(opt.opt.filename.as_path())
            .and_then(|mut file| file.read_to_string(&mut buf))
            .unwrap_or_else(|err| {
                eprintln!(
                    "Failed to read {}: {}",
                    opt.opt.filename.to_string_lossy(),
                    err
                );
                process::exit(1);
            });
        opt.opt.filename
    };
    let buf: Rc<_> = buf.into();
    let max_errors = opt.opt.max_errors;
    let color_choice = opt.color;
    real_main(buf, opt, &output)
        .unwrap_or_else(|(err, files)| err_exit(err, max_errors, color_choice, &files));
}
