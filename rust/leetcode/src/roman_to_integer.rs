// https://leetcode.com/problems/roman-to-integer/description/
use std::collections::HashMap;

struct Solution;

impl Solution {
    pub fn roman_to_int(s: String) -> i32 {
        let map = HashMap::from([
            ('I', 1),
            ('V', 5),
            ('X', 10),
            ('L', 50),
            ('C', 100),
            ('D', 500),
            ('M', 1000),
        ]);
        let mut result = 0;
        let chars = s.chars().collect::<Vec<char>>();
        let mut skip = false;

        for (i, c) in s.chars().enumerate() {
            if skip {
                skip = false;
                continue;
            }

            let a = map.get(&c).unwrap();

            if let Some(next) = chars.get(i + 1) {
                let b = map.get(next).unwrap();
                if a < b {
                    result -= *a
                } else {
                    result += *a;
                }
            } else {
                result += *a;
            }
        }
        result
    }
}

#[test]
fn examples() {
    assert_eq!(Solution::roman_to_int("III".to_string()), 3);
    assert_eq!(Solution::roman_to_int("LVIII".to_string()), 58);
    assert_eq!(Solution::roman_to_int("MCMXCIV".to_string()), 1994);
}
