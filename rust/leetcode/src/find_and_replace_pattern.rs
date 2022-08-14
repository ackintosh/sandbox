// https://leetcode.com/problems/find-and-replace-pattern/

use std::collections::HashMap;

struct Solution;

impl Solution {
    pub fn find_and_replace_pattern(words: Vec<String>, pattern: String) -> Vec<String> {
        let pattern_nums = Self::word_to_nums(&pattern);

        words
            .into_iter()
            .filter(|word| Self::word_to_nums(&word) == pattern_nums)
            .collect()
    }

    fn word_to_nums(word: &String) -> String {
        let mut map: HashMap<char, char> = HashMap::new();
        let mut num = 1;

        let mut nums = "".to_string();
        for w in word.chars() {
            match map.get(&w) {
                None => {
                    let c = format!("{}", num).pop().unwrap();
                    nums.push(c);
                    map.insert(w, c);
                    num += 1;
                }
                Some(c) => {
                    nums.push(*c);
                }
            }
        }

        nums
    }
}

#[test]
fn test() {
    assert_eq!(
        vec!["mee".to_string(), "aqq".to_string()],
        Solution::find_and_replace_pattern(
            vec![
                "abc".to_string(),
                "deq".to_string(),
                "mee".to_string(),
                "aqq".to_string(),
                "dkd".to_string(),
                "ccc".to_string()
            ],
            "abb".to_string()
        )
    );
}
