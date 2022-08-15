use criterion::{criterion_group, criterion_main};

// 実行方法
// https://github.com/BurntSushi/critcmp#usage
//
// $ cargo install critcmp
//
// 結果を `baseline-vec` の名前で保存する
// $ cargo bench --bench critcmp -- --save-baseline baseline-vec
//
// `iter` も同様に行う
// $ cargo bench --bench critcmp -- --save-baseline baseline-iter
//
// それぞれの baseline が保存されていることを確認する
// $ critcmp --baselines
//
// $ critcmp baseline-vec baseline-iter

use criterion::{black_box, Criterion};
use crate_critcmp::run_encode;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("encode", |b| {
        b.iter(|| {
            let metric_set = run_encode();
            black_box(metric_set);
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
