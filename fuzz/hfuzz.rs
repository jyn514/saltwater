#[macro_use]
extern crate honggfuzz;
extern crate rcc;

fn is_exotic_keyword(s: &str) -> bool {
    use rcc::data::lex::{Keyword::*, Token};
    use rcc::Locatable;
    let (first, _) = rcc::Lexer::new("<test-suite>", s.chars(), false).first_token();
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
    loop {
        fuzz!(|s: &[u8]| {
            if let Ok(s) = std::str::from_utf8(s) {
                if !is_exotic_keyword(s) {
                    rcc::compile(s, "<fuzz test>".into(), false, false, false);
                }
            }
        });
    }
}
