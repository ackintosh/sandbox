// https://leetcode.com/problems/rotate-image/

struct Solution;

impl Solution {
    pub fn rotate(matrix: &mut Vec<Vec<i32>>) {
        let n = matrix.len() - 1;
        let max_row_index = (matrix.len() as f32 / 2.0).ceil() as usize - 1;
        // println!("max_row_index: {}", max_row_index);
        if matrix[0].len() == 1 {
            return;
        }
        let max_col_index = matrix[0].len() - 2;
        // println!("max_col_index: {}", max_col_index);

        let mut col_start_index = 0;
        for row_index in 0..=max_row_index {
            for col_index in col_start_index..=(max_col_index - row_index) {
                let copy_pos1 = matrix[col_index][n - row_index];
                matrix[col_index][n - row_index] = matrix[row_index][col_index];
                // println!("{row_index} {col_index} ... copy_pos1: ({}, {}) : {}", col_index, n - row_index, copy_pos1);

                let copy_pos2 = matrix[n - row_index][n - col_index];
                matrix[n - row_index][n - col_index] = copy_pos1;
                // println!("{row_index} {col_index} ... copy_pos2: ({}, {}) : {}", n - row_index, n - col_index, copy_pos2);

                let copy_pos3 = matrix[n - col_index][row_index];
                matrix[n - col_index][row_index] = copy_pos2;
                // println!("{row_index} {col_index} ... copy_pos3: ({}, {}) : {}", n - col_index, row_index, copy_pos3);

                matrix[row_index][col_index] = copy_pos3;
            }
            col_start_index += 1;
        }
    }
}

#[test]
fn test() {
    let mut matrix = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
    let expected = vec![vec![7, 4, 1], vec![8, 5, 2], vec![9, 6, 3]];
    Solution::rotate(&mut matrix);
    assert_eq!(expected, matrix);

    let mut matrix = vec![
        vec![5, 1, 9, 11],
        vec![2, 4, 8, 10],
        vec![13, 3, 6, 7],
        vec![15, 14, 12, 16],
    ];
    let expected = vec![
        vec![15, 13, 2, 5],
        vec![14, 3, 4, 1],
        vec![12, 6, 8, 9],
        vec![16, 7, 10, 11],
    ];
    Solution::rotate(&mut matrix);
    assert_eq!(expected, matrix);

    let mut matrix = vec![vec![1]];
    let expected = vec![vec![1]];
    Solution::rotate(&mut matrix);
    assert_eq!(expected, matrix);
}
