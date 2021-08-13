#![feature(test)]
// ベンチマークの実行
//
// ```shell
// $ cargo +nightly bench
// ```

extern crate test;
use test::Bencher;

use std::cell::RefCell;
use lru_time_cache::LruCache;

const RANGE: usize = 32 * 1024;
const FIND_TIMES: usize = 10;
use rand::prelude::*;

#[bench]
fn lru_time_cache_sum(b: &mut Bencher) {
    let mut lru = LruCache::with_capacity(RANGE);
    for i in 0..RANGE {
        lru.insert(i, i);
    }
    let lru = RefCell::new(lru);
    b.iter(|| {
        let res: usize = (0..FIND_TIMES)
            .map(|_| *lru
                .borrow_mut()
                .get(&thread_rng().gen_range(0..RANGE))
                .unwrap_or(&0))
            .sum();
        test::black_box(res);
    });
}