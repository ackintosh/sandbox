// https://leetcode.com/problems/find-valid-matrix-given-row-and-column-sums/

struct Solution;

impl Solution {
    pub fn restore_matrix(mut row_sum: Vec<i32>, mut col_sum: Vec<i32>) -> Vec<Vec<i32>> {
        let mut result_matrix = vec![vec![0; col_sum.len()]; row_sum.len()];

        while !Self::completed(&row_sum, &col_sum) {
            let (min_r, min_c) = Self::find_min_pos(&row_sum, &col_sum);
            let min_val = row_sum[min_r].min(col_sum[min_c]);
            result_matrix[min_r][min_c] = min_val;
            row_sum[min_r] -= min_val;
            col_sum[min_c] -= min_val;

            // println!("min_val: {}", min_val);
            // println!("result_matrix: {:?}", result_matrix);
            // println!("row_sum: {:?}", row_sum);
            // println!("col_sum: {:?}", col_sum);
        }

        result_matrix
    }

    fn completed(row_sum: &Vec<i32>, col_sum: &Vec<i32>) -> bool {
        for r in row_sum {
            if r > &0 {
                return false;
            }
        }

        for c in col_sum {
            if c > &0 {
                return false;
            }
        }

        true
    }

    fn find_min_pos(row_sum: &Vec<i32>, col_sum: &Vec<i32>) -> (usize, usize) {
        let mut min_row_val = i32::max_value();
        let min_row_index = row_sum.iter().enumerate().fold(0_usize, |result, (i, v)| {
            if v > &0 && &min_row_val > v {
                min_row_val = *v;
                i
            } else {
                result
            }
        });

        let mut min_col_val = i32::max_value();
        let min_col_index = col_sum.iter().enumerate().fold(0_usize, |result, (i, v)| {
            if v > &0 && &min_col_val > v {
                min_col_val = *v;
                i
            } else {
                result
            }
        });

        (min_row_index, min_col_index)
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![vec![3, 0], vec![1, 7]],
        Solution::restore_matrix(vec![3, 8], vec![4, 7])
    );
    assert_eq!(
        vec![vec![0, 5, 0], vec![6, 1, 0], vec![2, 0, 8]],
        Solution::restore_matrix(vec![5, 7, 10], vec![8, 6, 8])
    );
}
