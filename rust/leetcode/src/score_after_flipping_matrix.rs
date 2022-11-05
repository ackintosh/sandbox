// https://leetcode.com/problems/score-after-flipping-matrix/

// 参考
// * 最適化されたコード
// https://leetcode.com/problems/score-after-flipping-matrix/discuss/143722/C%2B%2BJavaPython-Easy-and-Concise
// * 詳しい説明
// https://leetcode.com/problems/score-after-flipping-matrix/discuss/143812/C%2B%2BJava-From-Intuition-Un-optimized-code-to-Optimized-Code-with-Detailed-Explanation

struct Solution;

impl Solution {
    pub fn matrix_score(grid: Vec<Vec<i32>>) -> i32 {
        let num_row = grid.len();
        let num_col = grid[0].len();

        let mut score = (1 << (num_col as i32 - 1)) * num_row as i32;

        for c in 1..num_col {
            let mut same = 0_i32;

            for r in 0..num_row {
                if grid[r][0] == grid[r][c] {
                    same += 1;
                }
            }

            score += (1 << (num_col - c - 1)) * same.max(num_row as i32 - same);
        }

        score
    }
}

#[test]
fn test() {
    assert_eq!(
        39,
        Solution::matrix_score(vec![vec![0, 0, 1, 1], vec![1, 0, 1, 0], vec![1, 1, 0, 0]])
    );
}
