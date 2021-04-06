// 最強最速アルゴリズマー養成講座
// 第７章 動的計画法・メモ化
// P.177 ナップサック問題
mod knapsack {
    // 重さの合計 10 まで、価値の合計の最大は?

    use std::collections::HashMap;
    use std::convert::TryFrom;

    #[test]
    fn search1() {
        const WEIGHT: [i32; 5] = [3, 4, 1, 2, 3];
        const VALUE: [i32; 5] = [2, 3, 2, 3, 6];
        let mut max = 0;

        //       *
        //      / \
        //     1   0      item_index: 1 <-- 品物Aを 運ぶ/運ばない
        //    / \  / \
        //   1  0  1  0   item_index: 2 <-- 品物Bを 運ぶ/運ばない
        //   (略)
        solution(0, 0, 0, &mut max);

        assert_eq!(14, max);

        // *** 探索方法1の実装 ***
        // * 関数の返り値を持たず、
        // 「いま見ている商品番号」「いま持っている重さ」「いま持っている商品価値」を引き回している。
        // * これは、直感的な実装ではあるが、メモ化が難しいというデメリットがある
        //  `max` は、探索の結果得られた最適解ではなく、単純い試している途中の値にすぎないので、メモには向かない。
        fn solution(item_index: usize, weight_total: i32, value_total: i32, max: &mut i32) {
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
            if item_index >= WEIGHT.len() {
                return;
            }

            let w = WEIGHT[item_index];
            let v = VALUE[item_index];

            // 品物 `item_index` を運ぶ場合
            solution(item_index + 1, weight_total + w, value_total + v, max);

            // 品物 `item_index` を運ばない場合
            solution(item_index + 1, weight_total, value_total, max);
        }
    }

    #[test]
    fn search2() {
        const WEIGHT: [i32; 5] = [3, 4, 1, 2, 3];
        const VALUE: [i32; 5] = [2, 3, 2, 3, 6];

        let mut memo = vec![HashMap::new(); 5];

        let max = solution(0, 0, &mut memo);
        assert_eq!(14, max);

        // *** 探索方法2 の実装 ***
        // 返り値で「それ以降で得られる商品価値」を返すようにすることで、メモ化できるようになっている
        fn solution(
            item_index: usize,
            weight_total: i32,
            memo: &mut Vec<HashMap<i32, i32>>,
        ) -> i32 {
            // 深さが上限を超えた場合
            if item_index >= WEIGHT.len() {
                return 0;
            }

            // メモ
            if let Some(m) = memo[item_index].get(&weight_total) {
                println!(
                    "[memo] item_index: {}, weight_total: {}, max: {}",
                    item_index, weight_total, m
                );
                return *m;
            }

            let w = WEIGHT[item_index];
            let v = VALUE[item_index];

            // 品物 `item_index` を運ぶ場合
            let a = if weight_total + w <= 10 {
                solution(item_index + 1, weight_total + w, memo) + v
            } else {
                0
            };
            // 品物 `item_index` を運ばない場合
            let b = solution(item_index + 1, weight_total, memo);

            let max = a.max(b);
            memo[item_index].insert(weight_total, max);

            max
        }
    }

    // *** 動的計画法を使った解法 ***
    #[test]
    fn dp() {
        const WEIGHT: [i32; 5] = [3, 4, 1, 2, 3];
        const VALUE: [i32; 5] = [2, 3, 2, 3, 6];
        let weight_limit = 10;

        // 0番目~5つの品物 = 要素数6
        // 0~10までの重量 = 要素数11
        let mut table = [[0; 11]; 6];

        let mut result = 0;

        for i in 0..WEIGHT.len() {
            for j in 0..table[i].len() {
                let w = WEIGHT[i];
                let v = VALUE[i];

                let new_weight = j + usize::try_from(w).unwrap();
                if new_weight <= weight_limit {
                    let max = table[i][new_weight].max(table[i][j] + v);
                    table[i + 1][new_weight] = max;
                    result = max;
                }
            }
        }

        // println!("{:?}", table);
        assert_eq!(14, result);
    }
}
