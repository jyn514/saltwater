use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rcc::compile_aot as compile;

const FACTORIAL: &str = include_str!("../tests/runner-tests/factorial.c");
const FIBONACCI: &str = include_str!("../tests/runner-tests/fibonacci.c");

fn examples(c: &mut Criterion) {
    let opts = rcc::Opt {
        filename: "<benchmark>".into(),
        ..Default::default()
    };
    let mut group = c.benchmark_group("Fibonacci");
    group.bench_function("rcc", |b| {
        b.iter(|| black_box(compile(FIBONACCI, &opts)));
    });
    group.finish();

    let mut group = c.benchmark_group("Factorial");
    group.bench_function("rcc", |b| {
        b.iter(|| black_box(compile(FACTORIAL, &opts)));
    });
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = examples
}
criterion_main!(benches);
