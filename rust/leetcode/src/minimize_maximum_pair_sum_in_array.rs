// https://leetcode.com/problems/minimize-maximum-pair-sum-in-array/

use std::collections::VecDeque;

struct Solution;

impl Solution {
    pub fn min_pair_sum(mut nums: Vec<i32>) -> i32 {
        nums.sort();
        let mut q = VecDeque::from(nums);
        let mut result = i32::min_value();

        let mut min = q.pop_front();
        let mut max = q.pop_back();

        while min.is_some() && max.is_some() {
            result = result.max(min.unwrap() + max.unwrap());

            min = q.pop_front();
            max = q.pop_back();
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(7, Solution::min_pair_sum(vec![3, 5, 2, 3]));
    assert_eq!(
        8,
        Solution::min_pair_sum(vec![4, 1, 5, 1, 2, 5, 1, 5, 5, 4])
    );
}
