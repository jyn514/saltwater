use super::{CompileResult, Literal, Locatable, Token};
use crate::data::lex::test::{cpp, cpp_no_newline};
use crate::intern::InternedStr;

type LexType = CompileResult<Locatable<Token>>;

fn lex(input: &str) -> Option<LexType> {
    let mut lexed = lex_all(input);
    assert!(
        lexed.len() <= 1,
        "too many lexemes for {}: {:?}",
        input,
        lexed
    );
    lexed.pop()
}
fn lex_all(input: &str) -> Vec<LexType> {
    cpp(input).collect()
}

fn match_data<T>(lexed: Option<LexType>, closure: T) -> bool
where
    T: FnOnce(Result<&Token, &str>) -> bool,
{
    match_data_ref(&lexed, closure)
}
fn match_data_ref<T>(lexed: &Option<LexType>, closure: T) -> bool
where
    T: FnOnce(Result<&Token, &str>) -> bool,
{
    match lexed {
        Some(Ok(result)) => closure(Ok(&result.data)),
        Some(Err(err)) if err.is_lex_err() => closure(Err(&err.data.to_string())),
        _ => false,
    }
}

fn match_char(lexed: Option<LexType>, expected: u8) -> bool {
    match_data(lexed, |c| c == Ok(&Literal::Char(expected).into()))
}

fn match_str(lexed: Option<LexType>, expected: &str) -> bool {
    let string = format!("{}\0", expected).into();
    match_data(lexed, |c| c == Ok(&Literal::Str(string).into()))
}

fn match_all(lexed: &[LexType], expected: &[Token]) -> bool {
    lexed
        .iter()
        .zip(expected)
        .all(|(actual, expected)| match actual {
            Ok(token) => token.data == *expected,
            _ => false,
        })
}
fn assert_int(s: &str, expected: i64) {
    assert!(
        match_data(lex(s), |lexed| lexed == Ok(&Literal::Int(expected).into())),
        "{} != {}",
        s,
        expected
    );
}
fn assert_float(s: &str, expected: f64) {
    let lexed = lex(s);
    assert!(
        match_data_ref(&lexed, |lexed| lexed
            == Ok(&Literal::Float(expected).into())),
        "({}) {:?} != {}",
        s,
        lexed,
        expected
    );
}
fn assert_err(s: &str) {
    let lexed = lex_all(s);
    assert!(
        lexed.iter().any(|e| e.is_err()),
        "{:?} is not an error (from {})",
        &lexed,
        s
    );
}

#[test]
fn test_plus() {
    let parse = lex("+");
    assert_eq!(
        parse,
        Some(Ok(Locatable {
            data: Token::Plus,
            location: Default::default(),
        }))
    )
}

#[test]
fn test_ellipses() {
    assert!(match_all(
        &lex_all("...;...;.."),
        &[
            Token::Ellipsis,
            Token::Semicolon,
            Token::Ellipsis,
            Token::Semicolon,
            Token::Dot,
            Token::Dot,
        ]
    ));
}

#[test]
fn test_overflow() {
    assert!(match lex("10000000000000000000000") {
        Some(lexed) => lexed.is_err(),
        None => false,
    })
}

#[test]
fn test_int_literals() {
    assert_int("10", 10);
    assert_int("0x10", 16);
    assert_int("0b10", 2);
    assert_int("010", 8);
    assert_int("02l", 2);
    assert_int("0L", 0);
    assert_int("0xff", 255);
    assert_int("0xFF", 255);
    assert_err("0b");
    assert_err("0x");
    assert_err("09");
    assert_eq!(lex_all("1a").len(), 2);
}
#[test]
fn test_float_literals() {
    assert_float("0.1", 0.1);
    assert_float(".1", 0.1);
    for i in 0..10 {
        assert_float(&format!("1{}e{}", "0".repeat(i), 10 - i), 1e10);
    }
    assert!(match_all(
        &lex_all("-1"),
        &[Token::Minus, Literal::Int(1).into()]
    ));
    assert!(match_all(
        &lex_all("-1e10"),
        &[Token::Minus, Literal::Float(10_000_000_000.0).into()]
    ));
    assert!(match_data(lex("9223372036854775807u"), |lexed| lexed
        == Ok(
            &Literal::UnsignedInt(9_223_372_036_854_775_807u64).into()
        )));
    assert_float("0x.ep0", 0.875);
    assert_float("0x.ep-0l", 0.875);
    assert_float("0xe.p-4f", 0.875);
    assert_float("0xep-4f", 0.875);
    // DBL_MAX is actually 1.79769313486231570814527423731704357e+308L
    // TODO: change this whenever https://github.com/rust-lang/rust/issues/31407 is closed
    assert_float(
        "1.797693134862315708e+308L",
        #[allow(clippy::excessive_precision)]
        1.797_693_134_862_315_730_8e+308,
    );
    assert_float("9.88131291682e-324L", 9.881_312_916_82e-324);
    // DBL_MIN is actually 2.22507385850720138309023271733240406e-308L
    assert_float("2.225073858507201383e-308L", 2.225_073_858_507_201_4e-308);
}

#[test]
fn test_num_errors() {
    assert_err("1e");
    assert_err("1e.");
    assert_err("1e100000");
    assert_err("1e-100000");
    assert_eq!(lex_all("1e1.0").len(), 2);
}

fn lots_of(c: char) -> String {
    let mut buf = Vec::new();
    buf.resize(8096, c);
    buf.into_iter().collect()
}

#[test]
// used to have a stack overflow on large consecutive whitespace inputs
fn test_lots_of_whitespace() {
    assert_eq!(lex(&lots_of(' ')), None);
    assert_eq!(lex(&lots_of('\t')), None);
    assert_eq!(lex(&lots_of('\n')), None);
}

#[test]
fn backslashes() {
    let a = InternedStr::get_or_intern("a");
    assert!(match_data(
        lex(r"\
    a"),
        |lexed| lexed == Ok(&Token::Id(a))
    ));
    assert!(match_data(
        lex(r"\
    \
    \
    a"),
        |lexed| lexed == Ok(&Token::Id(a))
    ));
    assert!(match_data(lex("\\\na"), |lexed| lexed == Ok(&Token::Id(a))));
    assert_err(r"\a");
}

#[test]
fn test_comments() {
    assert!(lex("/* this is a comment /* /* /* */").is_none());
    assert!(lex("// this is a comment // /// // ").is_none());
    assert!(lex("/*/ this is part of the comment */").is_none());
    assert_eq!(
        lex_all(
            "/* make sure it finds things _after_ comments */
    int i;"
        )
        .len(),
        3
    );
    let bad_comment = lex("/* unterminated comments are an error ");
    assert!(
        bad_comment.is_some() && bad_comment.as_ref().unwrap().is_err(),
        "expected unterminated comment err, got {:?}",
        bad_comment
    );
    // check for stack overflow
    assert_eq!(lex(&"//".repeat(10_000)), None);
    assert_eq!(lex(&"/* */".repeat(10_000)), None);
}
#[test]
fn test_characters() {
    assert!(match_char(lex("'a'"), b'a'));
    assert!(match_char(lex("'0'"), b'0'));
    assert!(match_char(lex("'\\0'"), b'\0'));
    assert!(match_char(lex("'\\\\'"), b'\\'));
    assert!(match_char(lex("'\\n'"), b'\n'));
    assert!(match_char(lex("'\\r'"), b'\r'));
    assert!(match_char(lex("'\\\"'"), b'"'));
    assert!(match_char(lex("'\\''"), b'\''));
    assert!(match_char(lex("'\\a'"), b'\x07'));
    assert!(match_char(lex("'\\b'"), b'\x08'));
    assert!(match_char(lex("'\\v'"), b'\x0b'));
    assert!(match_char(lex("'\\f'"), b'\x0c'));
    assert!(match_char(lex("'\\t'"), b'\t'));
    assert!(match_char(lex("'\\?'"), b'?'));
    assert!(match_char(lex("'\\x00'"), b'\0'));
    // extra digits are allowed for hex escapes
    assert!(match_char(lex("'\\x00001'"), b'\x01'));
    // invalid ascii is allowed
    assert!(match_char(lex("'\\xff'"), b'\xff'));
    // out of range escapes should be caught
    assert!(lex("'\\xfff'").unwrap().unwrap_err().is_lex_err());
    assert!(lex("'\\777'").unwrap().unwrap_err().is_lex_err());
    // extra digits are not allowed for octal escapes
    assert!(lex("'\\0001'").unwrap().unwrap_err().is_lex_err());
    // should catch overflow in hex escapes
    assert!(lex("'\\xfff'").unwrap().unwrap_err().is_lex_err());
    assert!(lex("'\\xfffffffffffffffffffffffffff'")
        .unwrap()
        .unwrap_err()
        .is_lex_err());
}
#[test]
fn test_strings() {
    assert!(match_str(
        lex("\"this is a sample string\""),
        "this is a sample string"
    ));
    assert!(match_str(
        lex("\"consecutive \" \"strings\""),
        "consecutive strings"
    ));
    assert!(match_str(lex("\"string with \\0\""), "string with \0"));
    // 2 for newline
    assert_eq!(lex("\"").unwrap().unwrap_err().location.span, (0..2).into());
}

#[test]
fn test_no_newline() {
    assert!(cpp_no_newline("").next().is_none());
    let mut tokens: Vec<_> = cpp_no_newline(" ").collect();
    assert_eq!(tokens.len(), 1);
    assert!(tokens.remove(0).unwrap_err().is_lex_err());
}

// Integration tests
#[test]
fn test_for_loop() {
    assert!(lex_all(
        "for (int i = 0; i < 100; ++i {
        a[i] = i << 2 + i*4;
        }"
    )
    .into_iter()
    .all(|x| x.is_ok()))
}
