// https://leetcode.com/problems/rearrange-array-elements-by-sign/

use std::collections::VecDeque;

struct Solution;

impl Solution {
    pub fn rearrange_array(nums: Vec<i32>) -> Vec<i32> {
        let mut positive = VecDeque::new();
        let mut negative = VecDeque::new();

        for n in nums {
            if n > 0 {
                positive.push_back(n);
            } else {
                negative.push_back(n);
            }
        }

        let mut result = vec![];
        while let Some(n) = positive.pop_front() {
            result.push(n);
            result.push(negative.pop_front().unwrap());
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![3, -2, 1, -5, 2, -4],
        Solution::rearrange_array(vec![3, 1, -2, -5, 2, -4])
    );
}
