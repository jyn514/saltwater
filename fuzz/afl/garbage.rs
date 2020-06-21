#[macro_use]
extern crate afl;

use saltwater::{compile, initialize_aot_module, Opt};

fn main() {
    let opt = Opt {
        filename: "<fuzz test>".into(),
        ..Opt::default()
    };
    fuzz!(|s: &[u8]| {
        if let Ok(s) = std::str::from_utf8(s) {
            let module = initialize_aot_module("<afl>".into());
            compile(module, s, opt.clone());
        }
    });
}
