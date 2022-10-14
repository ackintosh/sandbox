// https://leetcode.com/problems/matrix-block-sum/
// Hints:
// 1. How to calculate the required sum for a cell (i,j) fast ?
// 2. Use the concept of cumulative sum array.
// 3. Create a cumulative sum matrix where dp[i][j] is the sum of all cells in the rectangle from (0,0) to (i,j), use inclusion-exclusion idea.

// explainer:
// https://leetcode.com/problems/matrix-block-sum/discuss/477041/Java-Prefix-sum-with-Picture-explain-Clean-code-O(m*n)

struct Solution;

impl Solution {
    pub fn matrix_block_sum(mat: Vec<Vec<i32>>, k: i32) -> Vec<Vec<i32>> {
        let sum_matrix = Self::create_cumulative_sum_matrix(&mat);
        // println!("{:?}", sum_matrix);

        let m = mat.len();
        let n = mat[0].len();

        let mut answer = vec![vec![0; n]; m];

        for r in 0..m {
            for c in 0..n {
                let r1 = r.saturating_sub(k as usize);
                let r2 = (r + k as usize).min(m - 1);
                let c1 = c.saturating_sub(k as usize);
                let c2 = (c + k as usize).min(n - 1);

                answer[r][c] = Self::sum_of_rectangle(&sum_matrix, r1, c1, r2, c2);
            }
        }

        answer
    }

    fn create_cumulative_sum_matrix(mat: &Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        let m = mat.len();
        let n = mat[0].len();
        let mut sum_matrix = vec![vec![0; n + 1]; m + 1];

        for r in 1..=m {
            for c in 1..=n {
                sum_matrix[r][c] = sum_matrix[r - 1][c] + sum_matrix[r][c - 1]
                    - sum_matrix[r - 1][c - 1]
                    + mat[r - 1][c - 1];
            }
        }

        sum_matrix
    }

    fn sum_of_rectangle(
        sum_matrix: &Vec<Vec<i32>>,
        mut r1: usize,
        mut c1: usize,
        mut r2: usize,
        mut c2: usize,
    ) -> i32 {
        // We need to increase these variables by 1 since `sum_matrix` starts with index 1.
        r1 += 1;
        c1 += 1;
        r2 += 1;
        c2 += 1;
        sum_matrix[r2][c2] - sum_matrix[r2][c1 - 1] - sum_matrix[r1 - 1][c2]
            + sum_matrix[r1 - 1][c1 - 1]
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![vec![12, 21, 16], vec![27, 45, 33], vec![24, 39, 28]],
        Solution::matrix_block_sum(vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]], 1)
    );
}
