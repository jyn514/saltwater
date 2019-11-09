use std::fs;

mod utils;

#[test]
fn all_headers() -> Result<(), std::io::Error> {
    for header_file in fs::read_dir("tests/c-headers/")? {
        let path = header_file?.path();
        if path.ends_with(".c") {
            let header_code = fs::read_to_string(path)?;
            utils::assert_compiles_no_main(&header_code);
        }
    }
    Ok(())
}
