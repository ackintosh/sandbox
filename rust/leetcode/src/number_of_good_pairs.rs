// https://leetcode.com/problems/number-of-good-pairs/

struct Solution;

impl Solution {
    pub fn num_identical_pairs(nums: Vec<i32>) -> i32 {
        assert!(nums.len() > 1);
        let mut count = 0;

        let last_index = nums.len() - 1;
        for i in (0..=(last_index - 1)).into_iter() {
            for j in ((i + 1)..=last_index).into_iter() {
                if nums[i] == nums[j] {
                    count += 1;
                }
            }
        }

        count
    }
}

#[test]
fn test() {
    let nums = vec![1, 2, 3, 1, 1, 3];
    assert_eq!(4, Solution::num_identical_pairs(nums));
}
