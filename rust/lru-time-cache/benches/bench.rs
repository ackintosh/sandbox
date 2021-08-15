#![feature(test)]
// ベンチマークの実行
//
// ```shell
// $ cargo +nightly bench
// ```

extern crate test;
use test::Bencher;

use std::cell::RefCell;
use std::collections::HashMap;

const RANGE: usize = 32 * 1024;
const FIND_TIMES: usize = 10;
use lru_time_cache::LruCache;
use rand::prelude::*;
use std::time::Duration;

// https://github.com/maidsafe/lru_time_cache/issues/143
// にあるベンチマークを参考にしている

#[bench]
fn lru_time_cache_sum(b: &mut Bencher) {
    let mut lru = LruCache::new(RANGE, Duration::from_secs(10));
    for i in 0..RANGE {
        lru.insert(i, i);
    }
    let lru = RefCell::new(lru);
    b.iter(|| {
        let res: usize = (0..FIND_TIMES)
            .map(|_| {
                *lru.borrow_mut()
                    .get(&thread_rng().gen_range(0..RANGE))
                    .unwrap_or(&0)
            })
            .sum();
        test::black_box(res);
    });
}

#[bench]
fn hashmap_sum(b: &mut Bencher) {
    let mut map = HashMap::new();
    for i in 0..RANGE {
        map.insert(i, i);
    }
    b.iter(|| {
        let res: usize = (0..FIND_TIMES)
            .map(|_| *map.get(&thread_rng().gen_range(0..RANGE)).unwrap_or(&0))
            .sum();
        test::black_box(res);
    });
}
