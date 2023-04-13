// https://leetcode.com/problems/minimum-suffix-flips/description/

struct Solution;

impl Solution {
    pub fn min_flips(target: String) -> i32 {
        let mut answer = 0;
        let mut working_char = '0';
        for c in target.chars() {
            if c != working_char {
                answer += 1;
                working_char = if working_char == '0' { '1' } else { '0' };
            }
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(3, Solution::min_flips("10111".into()));
    assert_eq!(3, Solution::min_flips("101".into()));
    assert_eq!(0, Solution::min_flips("0000".into()));
}
