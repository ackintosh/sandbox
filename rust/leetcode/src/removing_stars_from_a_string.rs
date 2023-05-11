// https://leetcode.com/problems/removing-stars-from-a-string/

struct Solution;

impl Solution {
    pub fn remove_stars(s: String) -> String {
        let mut answer = "".to_string();

        for c in s.chars() {
            if c == '*' {
                let _ = answer.pop();
            } else {
                answer.push(c);
            }
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(
        "lecoe".to_string(),
        Solution::remove_stars("leet**cod*e".to_string())
    );
    assert_eq!(
        "".to_string(),
        Solution::remove_stars("erase*****".to_string())
    );
}
