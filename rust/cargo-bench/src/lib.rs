#![feature(test)]
// ベンチマークの実行
//
// ```shell
// $ cargo +nightly bench
// ```

#[cfg(test)]
mod bench {
    extern crate test;

    use std::cell::RefCell;
    use test::Bencher;

    use std::collections::HashMap;
    use std::rc::Rc;

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

    #[bench]
    fn array_refcell_io(b: &mut Bencher) {
        b.iter(|| {
            let array_refcell = RefCell::new([0; RANGE]);
            for i in 0..RANGE {
                array_refcell.borrow_mut()[i] = i;
            }
            let res: usize = (0..FIND_TIMES)
                .map(|_| array_refcell.borrow()[thread_rng().gen_range(0_usize..RANGE)])
                .sum();
            test::black_box(res);
        });
    }

    #[bench]
    fn array_refcell_rc_io(b: &mut Bencher) {
        b.iter(|| {
            let array_refcell = Rc::new(RefCell::new([0; RANGE]));
            for i in 0..RANGE {
                array_refcell.borrow_mut()[i] = i;
            }
            let res: usize = (0..FIND_TIMES)
                .map(|_| array_refcell.borrow()[thread_rng().gen_range(0_usize..RANGE)])
                .sum();
            test::black_box(res);
        });
    }
}
