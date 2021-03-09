// https://leetcode.com/explore/challenge/card/march-leetcoding-challenge-2021/589/week-2-march-8th-march-14th/3665/

// ※最長回文を求める問題ではない...
// 解説を参照
// https://leetcode.com/problems/remove-palindromic-subsequences/discuss/490303/JavaC%2B%2BPython-Maximum-2-Operations
// > You need to know the difference between subarray and subsequence.
// > Subarray need to be consecutive。
// > Subsequence don't have to be consecutive.
// https://leetcode.com/problems/remove-palindromic-subsequences/discuss/490352/Java-Use-the-Trick-%3A-the-input-string-only-consists-of-letters-'a'-and-'b'!!

struct Solution;

impl Solution {
    pub fn remove_palindrome_sub(s: String) -> i32 {
        if s.is_empty() {
            return 0;
        }

        if Self::is_palindrome(s.as_str()) {
            1
        } else {
            2
        }
    }

    fn is_palindrome(s: &str) -> bool {
        let rev = s.chars().rev().collect::<String>();
        s == rev.as_str()
    }
}

#[test]
fn example1() {
    assert_eq!(Solution::remove_palindrome_sub("ababa".into()), 1);
}

#[test]
fn example2() {
    assert_eq!(Solution::remove_palindrome_sub("abb".into()), 2);
}

#[test]
fn example3() {
    assert_eq!(Solution::remove_palindrome_sub("baabb".into()), 2);
}

#[test]
fn example4() {
    assert_eq!(Solution::remove_palindrome_sub("".into()), 0);
}

#[test]
fn example5() {
    assert_eq!(Solution::remove_palindrome_sub("bbaabaaa".into()), 2);
}
