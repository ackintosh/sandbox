use criterion::{criterion_group, criterion_main};

// 実行方法
// https://github.com/BurntSushi/critcmp#usage
//
// $ cargo install critcmp
//
// `vec` のベンチマークを取り、結果を `baseline-vec` の名前で保存する
// $ cargo bench --bench critcmp -- vec --save-baseline baseline-vec
//
// `iter` も同様に行う
// $ cargo bench --bench critcmp -- iter --save-baseline baseline-iter
//
// それぞれの baseline が保存されていることを確認する
// $ critcmp --baselines
//
// $ critcmp baseline-vec baseline-iter

use criterion::{black_box, Criterion};
use prometheus_client::encoding::proto::EncodeProtobuf;
use prometheus_client::encoding::proto::{encode, EncodeMetric};
use prometheus_client::metrics::counter::Counter;
use prometheus_client::metrics::family::Family;
use prometheus_client::metrics::histogram::{exponential_buckets, Histogram};
use prometheus_client::registry::Registry;
use std::fmt::{Display, Formatter};

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("encode", |b| {
        #[derive(Clone, Hash, PartialEq, Eq, EncodeProtobuf)]
        struct Labels {
            path: String,
            method: Method,
            some_number: u64,
        }

        #[derive(Clone, Hash, PartialEq, Eq)]
        enum Method {
            Get,
            #[allow(dead_code)]
            Put,
        }

        impl Display for Method {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                match self {
                    Method::Get => write!(f, "Get"),
                    Method::Put => write!(f, "Put"),
                }
            }
        }

        let mut registry = Registry::<Box<dyn EncodeMetric>>::default();

        for i in 0..100 {
            let counter_family = Family::<Labels, Counter>::default();
            let histogram_family = Family::<Labels, Histogram>::new_with_constructor(|| {
                Histogram::new(exponential_buckets(1.0, 2.0, 10))
            });

            registry.register(
                format!("my_counter{}", i),
                "My counter",
                Box::new(counter_family.clone()),
            );
            registry.register(
                format!("my_histogram{}", i),
                "My histogram",
                Box::new(histogram_family.clone()),
            );

            for j in 0_u32..100 {
                counter_family
                    .get_or_create(&Labels {
                        path: format!("/path/{}", i),
                        method: Method::Get,
                        some_number: j.into(),
                    })
                    .inc();

                histogram_family
                    .get_or_create(&Labels {
                        path: format!("/path/{}", i),
                        method: Method::Get,
                        some_number: j.into(),
                    })
                    .observe(j.into());
            }
        }

        b.iter(|| {
            let metric_set = encode(&registry);
            black_box(metric_set);
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
