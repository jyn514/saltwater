mod common;
mod repl;

use saltwater::Opt;

fn main() {
    let options = Opt::default();

    #[cfg(feature = "color-backtrace")]
    common::backtrace::install(common::ColorChoice::Auto);

    let mut repl = repl::Repl::new(options);
    match repl.run() {
        Ok(_) => {}
        Err(err) => {
            println!("an unkown error occurred: {}", err);
            std::process::exit(1);
        }
    }
}
