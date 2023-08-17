// https://leetcode.com/problems/equal-row-and-column-pairs/description/

use std::collections::BTreeMap;

struct Solution;

impl Solution {
    pub fn equal_pairs(grid: Vec<Vec<i32>>) -> i32 {
        let mut rows: BTreeMap<Vec<i32>, i32> = BTreeMap::new();
        for r in grid.iter() {
            rows.entry(r.clone())
                .and_modify(|count| *count += 1)
                .or_insert(1);
        }

        let mut answer = 0;

        for ci in 0..(grid[0].len()) {
            let mut col = vec![];
            for ri in 0..(grid.len()) {
                col.push(grid[ri][ci]);
            }

            if let Some(count) = rows.get(&col) {
                // println!("col: {col:?}");
                answer += count;
            }
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(
        1,
        Solution::equal_pairs(vec![vec![3, 2, 1], vec![1, 7, 6], vec![2, 7, 7]])
    );
    assert_eq!(
        3,
        Solution::equal_pairs(vec![
            vec![3, 1, 2, 2],
            vec![1, 4, 4, 5],
            vec![2, 4, 2, 2],
            vec![2, 4, 2, 2]
        ])
    );
}
