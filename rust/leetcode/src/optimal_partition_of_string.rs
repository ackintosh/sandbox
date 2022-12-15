// https://leetcode.com/problems/optimal-partition-of-string/

use std::collections::HashSet;

struct Solution;

impl Solution {
    pub fn partition_string(s: String) -> i32 {
        let mut substrings = HashSet::new();
        let mut answer = 0;

        for c in s.chars() {
            if substrings.insert(c) {
            } else {
                substrings.clear();
                substrings.insert(c);
                answer += 1;
            }
        }

        if !substrings.is_empty() {
            answer += 1;
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(4, Solution::partition_string("abacaba".into()));
    assert_eq!(6, Solution::partition_string("ssssss".into()));
}
