// https://leetcode.com/problems/goal-parser-interpretation/

struct Solution;

impl Solution {
    pub fn interpret(command: String) -> String {
        let mut result = String::new();

        let mut splitted_iter = command.split("").filter(|c| !c.is_empty());

        while let Some(c) = splitted_iter.next() {
            match c {
                "G" => result.push_str(c),
                "(" => match splitted_iter.next() {
                    Some(cc) => match cc {
                        ")" => result.push('o'),
                        "a" => {
                            let _ = splitted_iter.next().unwrap();
                            let _ = splitted_iter.next().unwrap();
                            result.push_str("al");
                            continue;
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            }
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(Solution::interpret("G()(al)".into()), "Goal".to_owned());
}
