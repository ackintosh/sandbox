// https://leetcode.com/problems/maximum-69-number/

struct Solution;

impl Solution {
    pub fn maximum69_number (num: i32) -> i32 {
        let mut result = String::new();
        let mut changed = false;

        for s in num.to_string().split("").filter(|s| !s.is_empty()) {
            if changed {
                result.push_str(s);
                continue;
            }

            match s {
                "6" => {
                    result.push_str("9");
                    changed = true;
                }
                "9" => result.push_str(s),
                _ => unreachable!(),
            }
        }

        result.parse::<i32>().unwrap()
    }
}

#[test]
fn test() {
    assert_eq!(Solution::maximum69_number(9669), 9969);
}
