// https://leetcode.com/problems/count-items-matching-a-rule/

struct Solution;

impl Solution {
    pub fn count_matches(items: Vec<Vec<String>>, rule_key: String, rule_value: String) -> i32 {
        let rule_index: usize = match rule_key.as_str() {
            "type" => 0,
            "color" => 1,
            "name" => 2,
            _ => unreachable!(),
        };

        items
            .iter()
            .map(|item| {
                if item.get(rule_index).expect("value") == &rule_value {
                    1
                } else {
                    0
                }
            })
            .sum()
    }
}

#[test]
fn test() {
    let items = vec![
        vec!["phone", "blue", "pixel"],
        vec!["computer", "silver", "lenovo"],
        vec!["phone", "gold", "iphone"],
    ]
    .iter()
    .map(|v| v.iter().map(|&i| String::from(i)).collect::<Vec<_>>())
    .collect::<Vec<_>>();
    let rule_key = "color".to_owned();
    let rule_value = "silver".to_owned();

    assert_eq!(1, Solution::count_matches(items, rule_key, rule_value));
}
