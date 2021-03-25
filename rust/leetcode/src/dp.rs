// https://qiita.com/drken/items/dc53c683d6de8aeacf5a

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

// https://qiita.com/drken/items/dc53c683d6de8aeacf5a#a-%E5%95%8F%E9%A1%8C---frog-1
#[test]
fn frog1() {
    let h = vec![2, 9, 4, 5, 1, 6, 10];

    assert_eq!(dp(h), vec![0, 7, 2, 3, 5, 4, 8]);
}
