// https://leetcode.com/problems/difference-between-ones-and-zeros-in-row-and-column/

struct Solution;

impl Solution {
    pub fn ones_minus_zeros(grid: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        let row_num = grid.len();
        let col_num = grid[0].len();

        let mut diff = vec![vec![0; col_num]; row_num];

        let mut ones_row: Vec<i32> = vec![];
        for row in grid.iter() {
            let ones = row.iter().filter(|&r| *r == 1).count() as i32;
            ones_row.push(ones);
        }

        let mut ones_col: Vec<i32> = vec![];
        for ci in 0..col_num {
            let mut ones: i32 = 0;
            for ri in 0..row_num {
                if grid[ri][ci] == 1 {
                    ones += 1;
                }
            }
            ones_col.push(ones);
        }

        for ri in 0..row_num {
            for ci in 0..col_num {
                diff[ri][ci] = ones_row[ri] + ones_col[ci]
                    - (row_num as i32 - ones_row[ri])
                    - (col_num as i32 - ones_col[ci]);
            }
        }

        diff
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![vec![0, 0, 4], vec![0, 0, 4], vec![-2, -2, 2]],
        Solution::ones_minus_zeros(vec![vec![0, 1, 1], vec![1, 0, 1], vec![0, 0, 1]])
    );

    assert_eq!(
        vec![vec![5, 5, 5], vec![5, 5, 5]],
        Solution::ones_minus_zeros(vec![vec![1, 1, 1], vec![1, 1, 1]])
    );
}
