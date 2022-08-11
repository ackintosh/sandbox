use crate_criterion::fibonacci;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

// 実行方法
// $ cargo bench

// ドキュメント
// https://bheisler.github.io/criterion.rs/book/getting_started.html

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
