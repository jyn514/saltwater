#[macro_use]
extern crate honggfuzz;
extern crate rcc;

use rcc::codespan;
use codespan::FileId;
use rcc::{Files, Locatable};
use rcc::data::lex::{Keyword::*, Token};
use rcc::PreProcessorBuilder;
use std::default::Default;

fn is_exotic_keyword(s: &str, file: FileId, files: &mut Files) -> bool {
    let (first, _) = PreProcessorBuilder::new(s, file, files).build().first_token();
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
    let opt = Opt::default();

    loop {
        fuzz!(|s: &[u8]| {
            if let Ok(s) = std::str::from_utf8(s) {
                let mut files = Files::new();
                let file = files.add("<test-suite>", String::from(s).into());
                if !is_exotic_keyword(s, file, &mut files) {
                    let module = rcc::initialize_aot_module("<test-suite>".into());
                    let _ = rcc::compile(module, s, &opt, file, &mut files);
                }
            }
        });
    }
}
