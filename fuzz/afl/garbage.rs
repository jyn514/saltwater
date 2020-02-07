#[macro_use]
extern crate afl;
extern crate rcc;

use rcc::data::lex::{Keyword::*, Token};
use rcc::Locatable;
use rcc::PreProcessor;

fn lex(s: &str) -> PreProcessor {
    PreProcessor::new("<test-suite>", s.chars(), false)
}

fn is_exotic_keyword(s: &str) -> bool {
    let (first, _) = lex(s).first_token();
    let first = match first {
        Some(Locatable {
            data: Token::Keyword(k),
            ..
        }) => k,
        _ => return false,
    };
    match first {
        Restrict | Complex | Atomic | Imaginary | ThreadLocal | NoReturn | Generic
        | StaticAssert | Alignof | Alignas => true,
        _ => false,
    }
}

fn main() {
    fuzz!(|s: &[u8]| {
        if let Ok(s) = std::str::from_utf8(s) {
            if !is_exotic_keyword(s) {
                rcc::compile(s, "<fuzz test>".into(), false, false, false);
            }
        }
    });
}
