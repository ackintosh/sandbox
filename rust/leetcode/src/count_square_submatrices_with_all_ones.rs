// https://leetcode.com/problems/count-square-submatrices-with-all-ones/

struct Solution;

impl Solution {
    pub fn count_squares(matrix: Vec<Vec<i32>>) -> i32 {
        let mut answer = 0;

        let max_num_side = matrix.len().min(matrix[0].len());
        for num_side in 1..=max_num_side {
            for row in 0..matrix.len() {
                for col in 0..matrix[0].len() {
                    if Self::square_exists(&matrix, num_side, row, col) {
                        answer += 1;
                    }
                }
            }
        }

        answer
    }

    fn square_exists(matrix: &Vec<Vec<i32>>, side: usize, row: usize, col: usize) -> bool {
        if row + side > matrix.len() {
            return false;
        }

        if col + side > matrix[0].len() {
            return false;
        }

        for ri in row..(row + side) {
            for ci in col..(col + side) {
                if matrix[ri][ci] == 0 {
                    return false;
                }
            }
        }

        true
    }
}

#[test]
fn test() {
    assert_eq!(
        15,
        Solution::count_squares(vec![vec![0, 1, 1, 1], vec![1, 1, 1, 1], vec![0, 1, 1, 1],])
    );

    assert_eq!(
        7,
        Solution::count_squares(vec![vec![1, 0, 1], vec![1, 1, 0], vec![1, 1, 0],])
    );
}
