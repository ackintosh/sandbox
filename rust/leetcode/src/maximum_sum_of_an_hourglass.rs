// https://leetcode.com/problems/maximum-sum-of-an-hourglass/

struct Solution;

impl Solution {
    pub fn max_sum(grid: Vec<Vec<i32>>) -> i32 {
        let mut answer = 0;

        for col in 0..=grid.len() - 3 {
            for row in 0..=grid[0].len() - 3 {
                let sum = Self::sum_hourglass(&grid, col, row);
                answer = answer.max(sum);
            }
        }

        answer
    }

    fn sum_hourglass(grid: &Vec<Vec<i32>>, col: usize, row: usize) -> i32 {
        let mut sum = 0;

        for r in row..=row + 2 {
            sum += grid[col][r];
        }

        sum += grid[col + 1][row + 1];

        for r in row..=row + 2 {
            sum += grid[col + 2][r];
        }

        sum
    }
}

#[test]
fn test() {
    assert_eq!(
        30,
        Solution::max_sum(vec![
            vec![6, 2, 1, 3],
            vec![4, 2, 1, 5],
            vec![9, 2, 8, 7],
            vec![4, 1, 2, 9]
        ])
    );
    assert_eq!(
        35,
        Solution::max_sum(vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]])
    );
}
