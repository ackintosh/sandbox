// https://leetcode.com/problems/count-the-number-of-consistent-strings/

use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn count_consistent_strings(allowed: String, words: Vec<String>) -> i32 {
        let count = words
            .iter()
            .map(|word| {
                word.split("")
                    .filter(|&w| !w.is_empty())
                    .all(|w| allowed.contains(w))
            })
            .filter(|bool| *bool)
            .count();

        i32::try_from(count).unwrap()
    }
}

#[test]
fn test() {
    assert_eq!(
        Solution::count_consistent_strings(
            "ab".into(),
            vec![
                "ad".into(),
                "bd".into(),
                "aaab".into(),
                "baa".into(),
                "badab".into()
            ]
        ),
        2
    );
}
