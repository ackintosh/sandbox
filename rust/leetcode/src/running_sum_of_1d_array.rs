// https://leetcode.com/problems/running-sum-of-1d-array/

struct Solution;

impl Solution {
    pub fn running_sum(nums: Vec<i32>) -> Vec<i32> {
        let mut t = 0;
        let mut ret = vec![];
        for n in nums.iter() {
            t += n;
            ret.push(t);
        }

        ret
    }
}
