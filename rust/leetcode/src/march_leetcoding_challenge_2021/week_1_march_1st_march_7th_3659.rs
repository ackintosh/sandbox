// https://leetcode.com/explore/featured/card/march-leetcoding-challenge-2021/588/week-1-march-1st-march-7th/3659/

use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn missing_number(mut nums: Vec<i32>) -> i32 {
        nums.sort_unstable();

        // 途中の要素が不足している(exampl1)のパターン
        for (i, n) in nums.iter().enumerate() {
            let expected = i32::try_from(i).unwrap();
            if &expected != n {
                return expected;
            }
        }

        // 最後の要素が不足している(example2)のパターン
        i32::try_from(nums.len()).unwrap()
    }
}

#[test]
fn example1() {
    assert_eq!(Solution::missing_number(vec![3, 0, 1]), 2);
}

#[test]
fn example2() {
    assert_eq!(Solution::missing_number(vec![0, 1]), 2);
}
