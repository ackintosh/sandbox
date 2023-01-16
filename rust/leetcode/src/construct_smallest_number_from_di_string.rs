// https://leetcode.com/problems/construct-smallest-number-from-di-string/

struct Solution;

impl Solution {
    // https://leetcode.com/problems/construct-smallest-number-from-di-string/solutions/2422380/java-c-python-easy-reverse/?orderBy=most_votes
    pub fn smallest_number(pattern: String) -> String {
        let mut stack = vec![];
        let mut answer = vec![];
        let mut num = 1;

        for c in pattern.chars() {
            stack.push(num.to_string());
            if c == 'I' {
                while let Some(n) = stack.pop() {
                    answer.push(n);
                }
            } else if c == 'D' {
                // nop
            } else {
                unreachable!();
            }
            num += 1;
        }

        stack.push(num.to_string());
        while let Some(n) = stack.pop() {
            answer.push(n);
        }

        answer.join("")
    }
}

#[test]
fn test() {
    assert_eq!(
        "123549876".to_string(),
        Solution::smallest_number("IIIDIDDD".to_string())
    );
    assert_eq!(
        "4321".to_string(),
        Solution::smallest_number("DDD".to_string())
    );
}
