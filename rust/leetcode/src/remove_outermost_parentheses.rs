// https://leetcode.com/problems/remove-outermost-parentheses/

struct Solution;

impl Solution {
    pub fn remove_outer_parentheses(s: String) -> String {
        let mut primitives = vec![];

        let mut depth = 0;
        let mut t: String = "".into();

        for c in s.chars() {
            t.push(c);

            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        primitives.push(t.clone());
                        t.clear();
                    }
                }
                _ => {}
            }
        }

        // println!("{:?}", primitives);
        primitives
            .iter()
            // 前後の1文字を除いた文字列にする
            .map(|p| &p[1..(p.len() - 1)])
            .collect::<Vec<&str>>()
            .join("")
    }
}

#[test]
fn example1() {
    assert_eq!(
        "()()()".to_owned(),
        Solution::remove_outer_parentheses("(()())(())".into())
    );
}

#[test]
fn example2() {
    assert_eq!(
        "()()()()(())".to_owned(),
        Solution::remove_outer_parentheses("(()())(())(()(()))".into())
    );
}

#[test]
fn example3() {
    assert_eq!(
        "".to_owned(),
        Solution::remove_outer_parentheses("()()".into())
    );
}
