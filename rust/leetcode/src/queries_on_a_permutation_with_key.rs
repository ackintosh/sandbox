// https://leetcode.com/problems/queries-on-a-permutation-with-key/

use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn process_queries(queries: Vec<i32>, m: i32) -> Vec<i32> {
        let mut p = (1..=m).collect::<Vec<_>>();
        let mut result = vec![];

        queries.iter().for_each(|q| {
            let index = p.iter().position(|pp| pp == q).unwrap();
            result.push(i32::try_from(index).unwrap());
            p.remove(index);
            p.insert(0, *q);
        });

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        Solution::process_queries(vec![3, 1, 2, 1], 5),
        vec![2, 1, 2, 1]
    );
}
