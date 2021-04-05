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
                table[ki_usize] = min(
                    table[ki_usize],
                    base_cost + (h[ni_usize] - h[ki_usize]).abs(),
                );
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

// https://qiita.com/drken/items/dc53c683d6de8aeacf5a#c-%E5%95%8F%E9%A1%8C---vacation
mod vacation {
    use std::cmp::max;
    use std::convert::TryFrom;

    fn dp(n: i32, abc: Vec<Vec<i32>>) -> i32 {
        // 最大値を求める問題なのでゼロで初期化する
        let mut table = vec![vec![0; 3]; usize::try_from(n).unwrap()];

        println!("{:?}", table);

        for i in 0..usize::try_from(n).unwrap() {
            if i == 0 {
                // 前日の値が無いのでそのまま入れる
                table[i][0] = abc[i][0];
                table[i][1] = abc[i][1];
                table[i][2] = abc[i][2];
                continue;
            }

            for j in 0usize..3 {
                for jj in 0usize..3 {
                    if j == jj {
                        // 2日連続で同じ活動はできない
                        continue;
                    }

                    let yesterday = table[i - 1][j];
                    let today = yesterday + abc[i][jj];
                    table[i][jj] = max(table[i][jj], today);
                }
            }
        }

        println!("{:?}", table);
        *table
            .iter()
            .last()
            .expect("should have an element")
            .iter()
            .max()
            .expect("should have a value")
    }

    #[test]
    fn vacation() {
        let n = 3;
        let abc = vec![vec![10, 40, 70], vec![20, 50, 80], vec![30, 60, 90]];
        // let a = vec![10, 20, 30];
        // let b = vec![40, 50, 60];
        // let c = vec![70, 80, 90];

        assert_eq!(dp(n, abc), 210);
    }
}

// 最強最速アルゴリズマー養成講座
// 第７章 動的計画法・メモ化
// P.169 経路の探索
mod searching_for_a_route {
    // 9回、右または上に移動することができる
    // 右に5(w:5), 上に4(h:4)進む経路は何通りか

    use std::collections::HashMap;

    // *** 深さ優先探索 ***
    //
    #[test]
    fn dfs() {
        let result = solution(0, 0);
        assert_eq!(126, result);

        fn solution(h: i32, w: i32) -> i32 {
            if h == 5 && w == 4 {
                return 1;
            }
            if h + w == 9 {
                return 0;
            }

            solution(h + 1, w) + solution(h, w + 1)
        }
    }

    // *** メモ化した深さ優先探索 ***
    // 一度探索した経路はメモから結果を得られるので、各頂点に対して1回しか探索を行わないことになる
    // そのため、計算量は O(h * w) になる
    #[test]
    fn dfs_memoized() {
        // 探索結果をメモするmap
        let mut dp = HashMap::new();

        let result = solution(0, 0, &mut dp);
        assert_eq!(126, result);

        fn solution(h: i32, w: i32, dp: &mut HashMap<(i32, i32), i32>) -> i32 {
            if let Some(memo) = dp.get(&(h, w)) {
                return *memo;
            }
            if h == 5 && w == 4 {
                return 1;
            }
            if h + w == 9 {
                return 0;
            }

            let memo = solution(h + 1, w, dp) + solution(h, w + 1, dp);
            dp.insert((h, w), memo);
            memo
        }
    }

    // *** 動的計画法 ***
    // (h, w)にたどり着くには、(h - 1, w) もしくは (h, w - 1) を経由する必要がある
    // よって、その2つの頂点にたどり着くための道筋が何通り有るのかを足し合わせると (h, w) にたどり着くための道順が何通りあるのかを求められる
    #[test]
    fn dp() {
        let h: usize = 5;
        let w: usize = 4;
        let mut table = vec![vec![0; w + 1]; h + 1];

        // 原点の経路数は1
        table[0][0] = 1;

        for hi in 0..=h {
            for wi in 0..=w {
                if hi > 0 {
                    table[hi][wi] += table[hi - 1][wi];
                }
                if wi > 0 {
                    table[hi][wi] += table[hi][wi - 1];
                }
            }
        }

        // println!("{:?}", table);
        assert_eq!(126, table[h][w]);
    }
}

// 最強最速アルゴリズマー養成講座
// 第７章 動的計画法・メモ化
// P.177 ナップサック問題
mod knapsack {
    // 重さの合計 10 まで、価値の合計の最大は?

    #[test]
    fn search1() {
        let weight = vec![3, 4, 1, 2, 3];
        let value = vec![2, 3, 2, 3, 6];
        let mut max = 0;

        //       *
        //      / \
        //     1   0      item_index: 1 <-- 品物Aを 運ぶ/運ばない
        //    / \  / \
        //   1  0  1  0   item_index: 2 <-- 品物Bを 運ぶ/運ばない
        //   (略)
        solution(0, 0, 0, &weight, &value, &mut max);

        assert_eq!(14, max);

        // *** 探索方法1の実装 ***
        // * 関数の返り値を持たず、
        // 「いま見ている商品番号」「いま持っている重さ」「いま持っている商品価値」を引き回している。
        // * これは、直感的な実装ではあるが、メモ化が難しいというデメリットがある
        //  `max` は、探索の結果得られた最適解ではなく、単純い試している途中の値にすぎないので、メモには向かない。
        fn solution(item_index: usize, weight_total: i32, value_total: i32, weight: &Vec<i32>, value: &Vec<i32>, max: &mut i32) {
            // 重さが上限を超える場合
            if weight_total > 10 {
                return;
            }

            // 最大値を更新する
            *max = (*max).max(value_total);

            ///////////////////////////////////////////////
            // 以下、次の深さのための処理
            ///////////////////////////////////////////////

            // 深さが上限を超えた場合
            if item_index >= 5 {
                return;
            }

            let w = weight[item_index];
            let v = value[item_index];

            // 品物 `item_index` を運ぶ場合
            solution(item_index + 1, weight_total + w, value_total + v, weight, value, max);

            // 品物 `item_index` を運ばない場合
            solution(item_index + 1, weight_total, value_total, weight, value, max);
        }
    }
}
