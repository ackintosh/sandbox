// https://leetcode.com/problems/jewels-and-stones/
use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn num_jewels_in_stones(jewels: String, stones: String) -> i32 {
        let target = jewels
            .split("")
            .filter(|j| !j.is_empty())
            .collect::<Vec<_>>();

        i32::try_from(
            stones
                .split("")
                .filter(|s| !s.is_empty() && target.contains(s))
                .count(),
        )
        .unwrap()
    }
}

#[test]
fn test() {
    assert_eq!(
        Solution::num_jewels_in_stones("aA".into(), "aAAbbbb".into()),
        3
    );
}
