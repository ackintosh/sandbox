// https://leetcode.com/problems/shuffle-the-array/

use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn shuffle(nums: Vec<i32>, n: i32) -> Vec<i32> {
        let mut result = vec![];

        for i in 0..(nums.len() / 2) {
            result.push(nums[i]);
            result.push(nums[i + usize::try_from(n).unwrap()]);
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        Solution::shuffle(vec![2, 5, 1, 3, 4, 7], 3),
        vec![2, 3, 5, 4, 1, 7]
    );

    assert_eq!(
        Solution::shuffle(vec![1, 2, 3, 4, 4, 3, 2, 1], 4),
        vec![1, 4, 2, 3, 3, 2, 4, 1]
    );
}
