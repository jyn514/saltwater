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

fn too_many_parens(s: &str, n: usize) -> bool {
    let tokens = lex(s).filter(Result::is_ok);
    let mut parens_in_a_row = 0;
    for token in tokens {
        if let Ok(Locatable {
            data: Token::LeftParen,
            ..
        }) = token
        {
            parens_in_a_row += 1;
            if parens_in_a_row == n {
                return true;
            }
        } else {
            parens_in_a_row = 0;
        }
    }
    false
}

fn main() {
    fuzz!(|s: &[u8]| {
        if let Ok(s) = std::str::from_utf8(s) {
            if !is_exotic_keyword(s) && !too_many_parens(s, 800) {
                rcc::compile(s, "<fuzz test>".into(), false, false, false);
            }
        }
    });
}
