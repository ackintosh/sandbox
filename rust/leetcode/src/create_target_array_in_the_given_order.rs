// https://leetcode.com/problems/create-target-array-in-the-given-order/

use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn create_target_array(nums: Vec<i32>, index: Vec<i32>) -> Vec<i32> {
        let mut target = vec![];

        for (i, n) in nums.iter().enumerate() {
            target.insert(usize::try_from(index[i]).unwrap(), *n);
        }

        target
    }
}

#[test]
fn test() {
    assert_eq!(
        Solution::create_target_array(vec![0, 1, 2, 3, 4], vec![0, 1, 2, 2, 1]),
        vec![0, 4, 1, 3, 2]
    );
}
