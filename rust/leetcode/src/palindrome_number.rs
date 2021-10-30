// https://leetcode.com/problems/palindrome-number/
struct Solution;

impl Solution {
    pub fn is_palindrome(x: i32) -> bool {
        let s = x.to_string();
        let mut s_rev = String::new();
        for cc in s.chars().rev() {
            s_rev.push(cc);
        }

        s == s_rev
    }
}

mod test {
    use crate::palindrome_number::Solution;

    #[test]
    fn example1() {
        assert!(Solution::is_palindrome(121));
    }

    #[test]
    fn example2() {
        assert!(!Solution::is_palindrome(-121));
    }

    #[test]
    fn example3() {
        assert!(!Solution::is_palindrome(10));
    }
}
