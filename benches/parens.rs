use arcstr::ArcStr;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rcc::codespan::Files;
use rcc::{Lexer, Locatable, Parser, Token};

fn parens(c: &mut Criterion) {
    // should take no more than n stack frames
    let n = 3000;
    let the_biggun = arcstr::format!("{}1 + 2{}", "(".repeat(n), ")".repeat(n));
    let parse = |s| {
        let mut files = Files::new();
        let file_id = files.add("<bench>", ArcStr::clone(s));
        let mut lexer = Lexer::new(file_id, ArcStr::clone(s), false);
        let first: Locatable<Token> = lexer.next().unwrap().unwrap();
        let mut p: Parser<Lexer> = Parser::new(first, lexer, false);
        p.expr()
    };

    assert_eq!(parse(&the_biggun).unwrap().to_string(), "(1) + (2)");
    c.bench_function("rcc", |b| {
        b.iter(|| black_box(|| parse(&the_biggun)));
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = parens
}
criterion_main!(benches);
