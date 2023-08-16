// https://leetcode.com/problems/sort-vowels-in-a-string/

use std::collections::HashSet;

struct Solution;

impl Solution {
    pub fn sort_vowels(s: String) -> String {
        let mut vowels_pos = HashSet::new();
        let mut vowels = vec![];

        let def_vowels = vec!['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'];

        for (pos, ss) in s.chars().enumerate() {
            if def_vowels.contains(&ss) {
                vowels_pos.insert(pos);
                vowels.push(ss);
            }
        }

        vowels.sort_unstable();
        vowels.reverse();
        // println!("{:?}", s_vowels);

        let mut answer = String::new();
        for (pos, ss) in s.chars().enumerate() {
            if vowels_pos.contains(&pos) {
                answer.push(vowels.pop().unwrap());
            } else {
                answer.push(ss);
            }
        }
        answer
    }
}

#[test]
fn test() {
    assert_eq!(
        "lEOtcede".to_string(),
        Solution::sort_vowels("lEetcOde".to_string())
    );
    assert_eq!(
        "lYmpH".to_string(),
        Solution::sort_vowels("lYmpH".to_string())
    );
}
