// https://leetcode.com/problems/largest-submatrix-with-rearrangements/

struct Solution;

impl Solution {
    // ref https://leetcode.com/problems/largest-submatrix-with-rearrangements/solutions/1020710/c-clean-and-clear-with-intuitive-pictures-o-m-n-logn/
    pub fn largest_submatrix(matrix: Vec<Vec<i32>>) -> i32 {
        let row_num = matrix.len();
        let col_num = matrix[0].len();
        let mut heights = vec![0_i32; col_num];
        let mut answer = 0;

        for row in 0..row_num {
            for col in 0..col_num {
                if matrix[row][col] == 1 {
                    heights[col] += 1;
                } else {
                    heights[col] = 0;
                }
            }

            // sort the heights in ASC order
            let mut sorted_heights = heights.clone();
            sorted_heights.sort();

            for col in 0..col_num {
                answer = answer.max(sorted_heights[col] * (col_num as i32 - col as i32));
            }
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(
        4,
        Solution::largest_submatrix(vec![vec![0, 0, 1], vec![1, 1, 1], vec![1, 0, 1]])
    );
}
