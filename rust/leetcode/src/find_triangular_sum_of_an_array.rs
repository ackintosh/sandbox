// https://leetcode.com/problems/find-triangular-sum-of-an-array/

struct Solution;

impl Solution {
    pub fn triangular_sum(mut nums: Vec<i32>) -> i32 {
        while nums.len() > 1 {
            let mut new_nums = vec![];
            for (i, v) in nums.iter().enumerate() {
                if i + 1 == nums.len() {
                    break;
                }

                new_nums.push((v + nums[i + 1]) % 10);
            }

            nums = new_nums;
        }

        nums.pop().unwrap()
    }
}

#[test]
fn test() {
    assert_eq!(8, Solution::triangular_sum(vec![1, 2, 3, 4, 5]));
}
