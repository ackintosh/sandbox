// https://leetcode.com/problems/sort-the-matrix-diagonally/

struct Solution;

impl Solution {
    pub fn diagonal_sort(mut mat: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        {
            let until = mat.len();
            for start_row in 0..until {
                Self::solution(&mut mat, start_row, 0);
            }
        }

        {
            if let Some(first_row) = mat.get(0) {
                let until = first_row.len();
                for start_column in 0..until {
                    Self::solution(&mut mat, 0, start_column);
                }
            }
        }

        mat
    }

    #[allow(clippy::needless_range_loop)]
    fn solution(mat: &mut Vec<Vec<i32>>, start_row: usize, start_column: usize) {
        let mut values = {
            let mut i = 0;
            let mut values = vec![];
            loop {
                let row = start_row + i;
                let column = start_column + i;

                match mat.get(row) {
                    Some(r) => match r.get(column) {
                        Some(c) => values.push(*c),
                        None => break,
                    },
                    None => break,
                }
                i += 1;
            }
            values
        };
        values.sort_unstable();

        for i in 0..(values.len()) {
            let row = start_row + i;
            let column = start_column + i;

            match mat.get_mut(row) {
                Some(r) => match r.get_mut(column) {
                    Some(c) => *c = values[i],
                    None => break,
                },
                None => break,
            }
        }
    }
}

#[test]
fn test() {
    assert_eq!(
        Solution::diagonal_sort(vec![vec![3, 3, 1, 1], vec![2, 2, 1, 2], vec![1, 1, 1, 2]]),
        vec![vec![1, 1, 1, 1], vec![1, 2, 2, 2], vec![1, 2, 3, 3]]
    );
}
