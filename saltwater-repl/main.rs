//! The repl implementation for saltwater.
#![deny(rust_2018_idioms)]

mod commands;
mod helper;
mod repl;

fn main() {
    let mut repl = repl::Repl::new();
    match repl.run() {
        Ok(_) => {}
        Err(err) => {
            println!("error: {}", err);
            std::process::exit(1);
        }
    }
}
