// https://leetcode.com/problems/jewels-and-stones/

struct Solution;

impl Solution {
    pub fn num_jewels_in_stones(jewels: String, stones: String) -> i32 {
        let target = jewels.split("").filter(|j| !j.is_empty()).collect::<Vec<_>>();
        let mut count = 0;

        for s in stones.split("").filter(|s| !s.is_empty()) {
            if target.contains(&s) {
                count += 1;
            }
        }

        count
    }
}

#[test]
fn test() {
    assert_eq!(
        Solution::num_jewels_in_stones("aA".into(), "aAAbbbb".into()),
        3
    );
}
