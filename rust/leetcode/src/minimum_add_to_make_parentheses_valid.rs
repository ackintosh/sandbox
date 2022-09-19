// https://leetcode.com/problems/minimum-add-to-make-parentheses-valid/

struct Solution;

impl Solution {
    pub fn min_add_to_make_valid(s: String) -> i32 {
        let mut stack: u32 = 0;
        let mut moves = 0;

        for c in s.chars() {
            match c {
                '(' => stack += 1,
                ')' => {
                    if stack == 0 {
                        moves += 1;
                    } else {
                        stack -= 1;
                    }
                }
                _ => unreachable!(),
            }
        }

        moves + stack as i32
    }
}

#[test]
fn test() {
    assert_eq!(1, Solution::min_add_to_make_valid("())".into()));
    assert_eq!(3, Solution::min_add_to_make_valid("(((".into()));
    assert_eq!(4, Solution::min_add_to_make_valid("()))((".into()));
}
