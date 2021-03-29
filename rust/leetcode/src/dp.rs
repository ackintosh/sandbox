// https://qiita.com/drken/items/dc53c683d6de8aeacf5a

// https://qiita.com/drken/items/dc53c683d6de8aeacf5a#a-%E5%95%8F%E9%A1%8C---frog-1
mod frog1 {
    use std::cmp::min;

    fn dp(h: Vec<i32>) -> Vec<i32> {
        let mut table = vec![i32::max_value(); h.len()];

        for i in 0..h.len() {
            if i == 0 {
                // 最初のノードのコストは必ずゼロ
                table[i] = 0;
                continue;
            } else if i == 1 {
                // 2つ前の要素が無いので
                table[i] = min(table[i], (h[i - 1] - h[i]).abs());
            } else {
                let a = min(table[i], table[i - 1] + (h[i - 1] - h[i]).abs());
                let b = min(a, table[i - 2] + (h[i - 2] - h[i]).abs());
                table[i] = b;
            }
        }

        table
    }

    #[test]
    fn frog1() {
        let h = vec![2, 9, 4, 5, 1, 6, 10];

        assert_eq!(dp(h), vec![0, 7, 2, 3, 5, 4, 8]);
    }
}

// https://qiita.com/drken/items/dc53c683d6de8aeacf5a#b-%E5%95%8F%E9%A1%8C---frog-2
mod frog2 {
    use std::cmp::min;
    use std::convert::TryFrom;

    fn dp(n: i32, k: i32, h: Vec<i32>) -> i32 {
        let mut table = vec![i32::max_value(); h.len()];

        // 0番目のノードはコストゼロ
        table[0] = 0;

        for ni in 0..n {
            for ki in (ni + 1)..=(ni + k) {
                // println!("ni: {}, ki: {}", ni, ki);
                let ni_usize = usize::try_from(ni).unwrap();
                let ki_usize = usize::try_from(ki).unwrap();

                if ki_usize >= h.len() {
                    continue;
                }

                let base_cost = table[ni_usize];
                table[ki_usize] = min(table[ki_usize], base_cost + (h[ni_usize] - h[ki_usize]).abs());
            }
            // println!("{:?}", table);
        }

        table[h.len() - 1]
    }

    #[test]
    fn frog2() {
        let n = 5;
        let k = 3;
        let h = vec![10, 30, 40, 50, 20];

        assert_eq!(dp(n, k, h), 30);
    }
}
