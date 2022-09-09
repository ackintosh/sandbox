// https://leetcode.com/problems/minimum-number-of-steps-to-make-two-strings-anagram/

struct Solution;

impl Solution {
    pub fn min_steps(s: String, mut t: String) -> i32 {
        let mut steps = 0;

        for c in s.chars() {
            if !Self::remove(&mut t, &c) {
                steps += 1;
            }
        }

        steps
    }

    fn remove(t: &mut String, c: &char) -> bool {
        if let Some(pos) = t.find(*c) {
            t.remove(pos);
            true
        } else {
            false
        }
    }
}

#[test]
fn test() {
    assert_eq!(1, Solution::min_steps("bab".into(), "aba".into()));
    assert_eq!(5, Solution::min_steps("leetcode".into(), "practice".into()));
    assert_eq!(0, Solution::min_steps("anagram".into(), "mangaar".into()));
}
