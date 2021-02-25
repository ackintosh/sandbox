// https://leetcode.com/problems/minimum-number-of-operations-to-move-all-balls-to-each-box/

use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn min_operations(boxes: String) -> Vec<i32> {
        let str = boxes.as_str();
        let str_vec = str
            .split("")
            .filter(|&s| !s.is_empty())
            .collect::<Vec<&str>>();

        let mut result = vec![];

        for i in 0..str.len() {
            result.push(Self::solution(i, &str_vec));
        }

        result
    }

    fn solution(i: usize, str: &[&str]) -> i32 {
        let mut num_operation = 0;

        for (k, &v) in str.iter().enumerate() {
            if v == "0" {
                continue;
            }

            if i == k {
                continue;
            }

            let diff = i32::try_from(i).unwrap() - i32::try_from(k).unwrap();
            num_operation += diff.abs();
        }

        num_operation
    }
}

#[test]
fn example1() {
    assert_eq!(Solution::min_operations("110".into()), vec![1, 1, 3]);
}
