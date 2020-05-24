#[macro_use]
extern crate honggfuzz;
extern crate rcc;

use std::default::Default;

fn main() {
    use rcc::Opt;

    loop {
        fuzz!(|s: &[u8]| {
            if let Ok(s) = std::str::from_utf8(s) {
                let module = rcc::initialize_aot_module("<test-suite>".into());
                let opt = Opt::default();
                let _ = rcc::compile(module, s, opt);
            }
        });
    }
}
