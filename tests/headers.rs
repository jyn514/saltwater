use std::fs::{self, File};
use std::io::Error;
use std::path::{Path, PathBuf};

mod utils;

fn cpp_and_save(header: &str, dest: &Path) -> Result<(), Error> {
    use std::io::{ErrorKind, Write};
    use std::process::{Command, Stdio};
    let mut cpp = Command::new("cpp")
        .args(&["-P", "-undef", "-x", "c"])
        .stdin(Stdio::piped())
        .stdout(File::create(dest)?)
        .spawn()
        .expect("failed to start preprocessor");
    let stdin = cpp.stdin.as_mut().expect("couldn't access stdin");
    write!(stdin, "#include <{}.h>", header)?;
    cpp.wait().and_then(|status| {
        if status.success() {
            Ok(())
        } else {
            Err(Error::new(ErrorKind::InvalidData, "cpp exited with error"))
        }
    })
}

#[test]
fn all_headers() -> Result<(), Error> {
    const STANDARD_HEADERS: &[&str] = &[
        "assert",
        // _Complex is not yet supported
        // "complex",
        "ctype",
        "errno",
        // fenv uses bitfields on my machine
        //"fenv",
        "float",
        "inttypes",
        "limits",
        "locale",
        "math",
        "setjmp",
        "signal",
        "stdalign",
        "stdarg",
        // _Atomic is not yet supported
        //"stdatomic",
        "stdbool",
        // uses __attribute__
        //"stddef",
        "stdint",
        "stdio",
        "stdlib",
        "stdnoreturn",
        "string",
        "time",
        // assumes a builtin char16_t type that doesn't exist
        //"uchar",
        "wchar",
        "wctype",
    ];
    fs::create_dir_all("tests/c-headers")?;
    for header in STANDARD_HEADERS {
        let dest = PathBuf::from(format!("tests/c-headers/{}.c", header));
        cpp_and_save(header, &dest)?;
    }
    for header_file in fs::read_dir("tests/c-headers/")? {
        let header_file = header_file?;
        let path = header_file.path();
        println!("compiling {}", path.display());
        let header_code = fs::read_to_string(path)?;
        utils::assert_compiles_no_main(&header_code);
    }
    Ok(())
}
