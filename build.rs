use saltwater::{preprocess, Opt};
use std::fs::{create_dir_all, read_to_string, File};
use std::io::Write;
use std::path::PathBuf;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let out_dir = PathBuf::from(std::env::var("OUT_DIR")?);
    create_dir_all(out_dir.join("headers"))?;
    for header in globwalk::glob("headers/*.h")? {
        let header = header.expect("failed to get list of headers");
        let path = header.path();
        let src = read_to_string(path).expect("failed to read header file");
        let program = preprocess(&src, Opt::default());
        let tokens = program.result.expect("no");
        let definitions = program.preprocessor.definitions;
        let out_file = out_dir.join(path);
        println!("writing to {}", out_file.display());
        let strings = saltwater::intern::STRINGS.read()?;
        let rodeo = &*strings;
        let serialized: Vec<u8> = bincode::serialize(&(tokens, definitions))?;
        //tokens.write(&[b'\0'])?;
        let mut out_file = File::create(out_file)?;
        //out_file.write(&tokens.len().to_le_bytes())?;
        out_file.write_all(&serialized)?;
        //write(&out_file, encoded).expect("failed to write output");
    }
    Ok(())
}
