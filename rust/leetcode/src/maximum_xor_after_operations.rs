// https://leetcode.com/problems/maximum-xor-after-operations/

struct Solution;

impl Solution {
    pub fn maximum_xor(nums: Vec<i32>) -> i32 {
        nums.iter().fold(0, |acc, n| acc | n)
    }
}

#[test]
fn test() {
    assert_eq!(7, Solution::maximum_xor(vec![3, 2, 4, 6]));
    assert_eq!(11, Solution::maximum_xor(vec![1, 2, 3, 9, 2]));
}
