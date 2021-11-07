// 仲の悪い隣人たち

struct Solution;

impl Solution {
    fn dp(donations: Vec<i32>) -> i32 {
        let a = Self::take_first(&donations);
        let b = Self::skip_first(&donations);
        println!("a: {}, b: {}", a, b);

        a.max(b)
    }

    // 最初の家が寄付 "する"( = donationsの最初の要素を採用する)パターン
    fn take_first(donations: &Vec<i32>) -> i32 {
        let mut table = vec![vec![0; donations.len()]; donations.len()];

        for i in 0..donations.len() {
            // 最初の要素を採用する
            if i == 0 {
                table[i][i] = donations[i];
                continue;
            }

            // 最初の要素を採用しているので、最後の要素は採用しない( = tableの直前のindexの値をそのまま使う)
            if i == (donations.len() - 1) {
                table[i][i] = table[i - 1][i - 1];
                continue;
            }

            let p = table[i - 1][i - 1];
            let pp = if i == 1 { 0 } else { table[i - 2][i - 2] };

            let n = p.max(pp + donations[i]);
            table[i][i] = n;
        }

        println!("take_first: {:?}", table);

        *table.last().unwrap().last().unwrap()
    }

    // 最初の家が寄付 "しない"( = donationsの最初の要素を採用しない)パターン
    fn skip_first(donations: &Vec<i32>) -> i32 {
        let mut table = vec![vec![0; donations.len()]; donations.len()];

        for i in 0..donations.len() {
            // 最初の要素は採用しない
            if i == 0 {
                table[i][i] = 0;
                continue;
            }

            let p = table[i - 1][i - 1];
            let pp = if i == 1 { 0 } else { table[i - 2][i - 2] };

            let n = p.max(pp + donations[i]);
            table[i][i] = n;
        }

        println!("skip_first: {:?}", table);

        *table.last().unwrap().last().unwrap()
    }
}

#[test]
fn example1() {
    assert_eq!(19, Solution::dp(vec![10, 3, 2, 5, 7, 8]));
}
