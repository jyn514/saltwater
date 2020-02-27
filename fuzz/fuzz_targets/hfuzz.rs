extern crate codespan;
#[macro_use]
extern crate honggfuzz;
extern crate rcc;

use codespan::FileId;
use rcc::{Files, Locatable};
use rcc::data::lex::{Keyword::*, Token};
use rcc::PreProcessor;
use std::default::Default;

fn is_exotic_keyword(s: &str, file: FileId, files: &mut Files) -> bool {
    let (first, _) = PreProcessor::new(file, s, false, vec![], files).first_token();
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
                    let _ = rcc::compile(s, &opt, file, &mut files);
                }
            }
        });
    }
}
