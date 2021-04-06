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
