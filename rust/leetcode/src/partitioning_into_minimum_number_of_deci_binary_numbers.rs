// https://leetcode.com/problems/partitioning-into-minimum-number-of-deci-binary-numbers/

struct Solution;

impl Solution {
    pub fn min_partitions(n: String) -> i32 {
        let mut nums = n
            .split("")
            .filter(|s| !s.is_empty())
            .map(|s| s.parse::<i32>().unwrap())
            .collect::<Vec<_>>();
        nums.sort_unstable();

        *nums.last().unwrap()
    }
}

#[test]
fn test() {
    assert_eq!(Solution::min_partitions("82734".into()), 8);
}
