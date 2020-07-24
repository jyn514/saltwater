mod repl;

fn main() {
    let mut repl = repl::Repl::new();
    match repl.run() {
        Ok(_) => {}
        Err(err) => {
            println!("Unknown error in the REPL occurred: {}", err);
            std::process::exit(1);
        }
    }
}
