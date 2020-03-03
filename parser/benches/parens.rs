use criterion::{black_box, criterion_group, criterion_main, Criterion};
use parser::{Lexer, Locatable, Location, Parser, Token};
use std::rc::Rc;

fn parens(c: &mut Criterion) {
    // should take no more than n stack frames
    let n = 3000;
    let the_biggun = Rc::from(format!("{}1 + 2{}", "(".repeat(n), ")".repeat(n)));
    let parse = |s| {
        let mut lexer = Lexer::new((), Rc::clone(s), false);
        let first: Locatable<Token, Location> = lexer.next().unwrap().unwrap();
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
