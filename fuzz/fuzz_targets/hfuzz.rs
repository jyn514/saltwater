#[macro_use]
extern crate honggfuzz;
use saltwater::{Opt, compile, initialize_aot_module};

use std::default::Default;

fn main() {
    loop {
        fuzz!(|s: &[u8]| {
            if let Ok(s) = std::str::from_utf8(s) {
                let module = initialize_aot_module("<test-suite>".into());
                let opt = Opt::default();
                let _ = compile(module, s, opt);
            }
        });
    }
}
