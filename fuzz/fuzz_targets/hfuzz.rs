#[macro_use]
extern crate honggfuzz;
extern crate rcc;

use rcc::Locatable;
use rcc::data::lex::{Keyword::*, Token};
use rcc::PreProcessorBuilder;
use std::default::Default;

fn is_exotic_keyword(s: &str) -> bool {
    let (first, _) = PreProcessorBuilder::new(s).build().first_token();
    let first = match first {
        Some(Locatable {
            data: Token::Keyword(k),
            ..
        }) => k,
        _ => return false,
    };
    match first {
        Restrict | Complex | Atomic | Imaginary | ThreadLocal | Generic | StaticAssert
        | Alignof | Alignas => true,
        _ => false,
    }
}

fn main() {
    use rcc::Opt;

    loop {
        fuzz!(|s: &[u8]| {
            if let Ok(s) = std::str::from_utf8(s) {
                if !is_exotic_keyword(s) {
                    let module = rcc::initialize_aot_module("<test-suite>".into());
                    let opt = Opt::default();
                    let _ = rcc::compile(module, s, opt);
                }
            }
        });
    }
}
