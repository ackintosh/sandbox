// https://leetcode.com/problems/split-a-string-in-balanced-strings/

// スマートな回答
// https://leetcode.com/problems/split-a-string-in-balanced-strings/discuss/403836/C%2B%2BJavaPython-Easy-Solution

struct Solution;

impl Solution {
    pub fn balanced_string_split(s: String) -> i32 {
        let mut result = 0;
        let iter = s.split("").filter(|s| !s.is_empty());

        let mut working = "";
        let mut working_count = 0;

        for ss in iter {
            if working.is_empty() {
                working = ss;
                working_count = 1;
                continue;
            }

            if working == ss {
                working_count += 1;
            } else {
                working_count -= 1;
                if working_count == 0 {
                    result += 1;
                    working = "";
                }
            }
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(Solution::balanced_string_split("RLRRLLRLRL".into()), 4);
    assert_eq!(Solution::balanced_string_split("RLLLLRRRLR".into()), 3);
}
