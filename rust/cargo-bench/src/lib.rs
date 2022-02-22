#![feature(test)]
// ベンチマークの実行
//
// ```shell
// $ cargo +nightly bench
// ```

#[cfg(test)]
mod bench {
    extern crate test;
    use test::Bencher;

    use std::collections::HashMap;

    const RANGE: usize = 10_0000;
    const FIND_TIMES: usize = 10_0000;
    use rand::prelude::*;

    // HashMapへの書き込み/読み込み
    #[bench]
    fn hashmap_io(b: &mut Bencher) {
        b.iter(|| {
            let mut map = HashMap::new();
            for i in 0..RANGE {
                map.insert(i, i);
            }
            let res: usize = (0..FIND_TIMES)
                .map(|_| *map.get(&thread_rng().gen_range(0..RANGE)).unwrap_or(&0))
                .sum();
            test::black_box(res);
        });
    }

    // 配列への書き込み/読み込み
    // HashMapの10倍くらい速い
    #[bench]
    fn array_io(b: &mut Bencher) {
        b.iter(|| {
            let mut array = [0; RANGE];
            for i in 0..RANGE {
                array[i] = i;
            }
            let res: usize = (0..FIND_TIMES)
                .map(|_| array[thread_rng().gen_range(0_usize..RANGE)])
                .sum();
            test::black_box(res);
        });
    }
}
