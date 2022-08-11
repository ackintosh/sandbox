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

mod vec {
    use criterion::Criterion;
    use prometheus_client_vec::encoding::proto::encode;
    use prometheus_client_vec::metrics::counter::Counter;
    use prometheus_client_vec::metrics::family::Family;
    use prometheus_client_vec::registry::Registry;
    use std::borrow::Cow;

    pub fn criterion_benchmark(c: &mut Criterion) {
        c.bench_function("vec", |b| {
            b.iter(|| {
                let mut registry = Registry::default();
                let sub_registry = registry.sub_registry_with_prefix("my_prefix");
                let sub_sub_registry = sub_registry
                    .sub_registry_with_label((Cow::Borrowed("my_key"), Cow::Borrowed("my_value")));
                let family = Family::<Vec<(String, String)>, Counter>::default();
                sub_sub_registry.register("my_counter_family", "My counter family", family.clone());

                family
                    .get_or_create(&vec![
                        ("method".to_string(), "GET".to_string()),
                        ("status".to_string(), "200".to_string()),
                    ])
                    .inc();

                let metric_set = encode(&registry);

                let family = metric_set.metric_families.first().unwrap();
                assert_eq!("my_prefix_my_counter_family", family.name);
                assert_eq!("My counter family.", family.help);

                let metric = family.metrics.first().unwrap();
                assert_eq!(3, metric.labels.len());
                assert_eq!("method", metric.labels[0].name);
                assert_eq!("GET", metric.labels[0].value);
                assert_eq!("status", metric.labels[1].name);
                assert_eq!("200", metric.labels[1].value);
                assert_eq!("my_key", metric.labels[2].name);
                assert_eq!("my_value", metric.labels[2].value);
            })
        });
    }
}

mod iter {
    use criterion::Criterion;
    use prometheus_client_iter::encoding::proto::encode;
    use prometheus_client_iter::metrics::counter::Counter;
    use prometheus_client_iter::metrics::family::Family;
    use prometheus_client_iter::registry::Registry;
    use std::borrow::Cow;

    pub fn criterion_benchmark(c: &mut Criterion) {
        c.bench_function("iter", |b| {
            b.iter(|| {
                let mut registry = Registry::default();
                let sub_registry = registry.sub_registry_with_prefix("my_prefix");
                let sub_sub_registry = sub_registry
                    .sub_registry_with_label((Cow::Borrowed("my_key"), Cow::Borrowed("my_value")));
                let family = Family::<Vec<(String, String)>, Counter>::default();
                sub_sub_registry.register("my_counter_family", "My counter family", family.clone());

                family
                    .get_or_create(&vec![
                        ("method".to_string(), "GET".to_string()),
                        ("status".to_string(), "200".to_string()),
                    ])
                    .inc();

                let metric_set = encode(&registry);

                let family = metric_set.metric_families.first().unwrap();
                assert_eq!("my_prefix_my_counter_family", family.name);
                assert_eq!("My counter family.", family.help);

                let metric = family.metrics.first().unwrap();
                assert_eq!(3, metric.labels.len());
                assert_eq!("method", metric.labels[1].name);
                assert_eq!("GET", metric.labels[1].value);
                assert_eq!("status", metric.labels[2].name);
                assert_eq!("200", metric.labels[2].value);
                assert_eq!("my_key", metric.labels[0].name);
                assert_eq!("my_value", metric.labels[0].value);
            })
        });
    }
}

criterion_group!(benches, crate::vec::criterion_benchmark, crate::iter::criterion_benchmark);
criterion_main!(benches);
