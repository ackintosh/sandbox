// クレートの外部からベンチマークを実行する場合に利用する

// #![feature(test)]
//
// // ベンチマークの実行
// //
// // ```shell
// // $ cargo +nightly bench
// // ```
//
// extern crate test;
// use test::Bencher;
//
// use std::cell::RefCell;
// use std::collections::HashMap;
//
// const RANGE: usize = 32 * 1024;
// const FIND_TIMES: usize = 10;
// use rand::prelude::*;
// use std::time::Duration;
// use std::thread::sleep;
// use cargo_bench::ForBench;
//
//
// #[bench]
// fn bench(b: &mut Bencher) {
//     let a = ForBench {};
//     let mut map = HashMap::new();
//     for i in 0..RANGE {
//         map.insert(i, i);
//     }
//     b.iter(|| {
//         let res: usize = (0..FIND_TIMES)
//             .map(|_| *map.get(&thread_rng().gen_range(0..RANGE)).unwrap_or(&0))
//             .sum();
//         test::black_box(res);
//     });
// }
