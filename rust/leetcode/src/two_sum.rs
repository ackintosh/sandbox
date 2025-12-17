// https://leetcode.com/problems/two-sum/description/

use std::collections::HashMap;

struct Solution;

impl Solution {
    // Approach1: Brute Force
    pub fn two_sum_brute_force(nums: Vec<i32>, target: i32) -> Vec<i32> {
        for i in 0..nums.len() {
            for j in i + 1..nums.len() {
                if nums[i] + nums[j] == target {
                    return vec![i as i32, j as i32];
                }
            }
        }
        panic!("Solution not found. nums:{:?} target:{}", nums, target);
    }

    // Approach2: Two-pass Hash Table
    // https://leetcode.com/problems/two-sum/solutions/127810/two-sum-by-leetcode-kwuq/
    pub fn two_sum(nums: Vec<i32>, target: i32) -> Vec<i32> {
        let mut map: HashMap<i32, usize> = HashMap::new();
        for (i, n) in nums.iter().enumerate() {
            map.insert(*n, i);
        }

        for (i, n) in nums.iter().enumerate() {
            let complement = target - *n;
            if let Some(complement_i) = map.get(&complement) {
                if *complement_i != i {
                    return vec![i as i32, *complement_i as i32];
                }
            }
        }

        panic!("Solution not found. nums:{:?} target:{}", nums, target);
    }
}

#[test]
fn test_brute_force() {
    let res = Solution::two_sum_brute_force(vec![2, 7, 11, 15], 9);
    assert_eq!(res, vec![0, 1]);
    let res = Solution::two_sum_brute_force(vec![3, 2, 4], 6);
    assert_eq!(res, vec![1, 2]);
    let res = Solution::two_sum_brute_force(vec![3, 3], 6);
    assert_eq!(res, vec![0, 1]);
}

#[test]
fn test() {
    let res = Solution::two_sum(vec![2, 7, 11, 15], 9);
    assert_eq!(res, vec![0, 1]);
    let res = Solution::two_sum(vec![3, 2, 4], 6);
    assert_eq!(res, vec![1, 2]);
    let res = Solution::two_sum(vec![3, 3], 6);
    assert_eq!(res, vec![0, 1]);
}
