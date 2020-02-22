use std::io;
use std::path;
use std::process::Command;

extern crate env_logger;
extern crate log;
extern crate walkdir;
use log::debug;

#[test]
fn run_all() -> Result<(), io::Error> {
    let _ = env_logger::try_init();
    assert!(Command::new("cargo")
        .arg("build")
        .status()
        .unwrap()
        .success());
    for maybe_file in walkdir::WalkDir::new("tests/stack-overflow").follow_links(true) {
        debug!("file is {:?}", &maybe_file);
        let file = maybe_file?;
        if file.file_type().is_dir() {
            debug!("skipping directory {}", file.path().display());
            continue;
        }
        let path = file.path();
        if path.extension().map_or(false, |e| e == "c") {
            run_one(path)?;
        } else {
            debug!("path is {}, skipping", path.display());
        }
    }
    Ok(())
}

fn run_one(path: &path::Path) -> Result<(), io::Error> {
    println!("testing {}", path.display());
    let target = std::env::var("CARGO_TARGET_DIR").unwrap_or("target".into());
    let status = Command::new(format!("{}/debug/rcc", target))
        .arg(path)
        .status()
        .unwrap();
    assert_eq!(status.code(), Some(102));
    Ok(())
}
