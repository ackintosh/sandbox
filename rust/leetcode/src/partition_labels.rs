// https://leetcode.com/problems/partition-labels/

use std::collections::HashMap;
use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn partition_labels(s: String) -> Vec<i32> {
        let str = s.as_str();
        let mut result = vec![];

        let char_to_last_index = {
            let uniq_strs = {
                let mut strs = str
                    .split("")
                    .filter(|&s| !s.is_empty())
                    .collect::<Vec<&str>>();
                strs.sort_unstable();
                strs.dedup();
                strs
            };

            let mut char_to_last_index = HashMap::new();

            for s in uniq_strs {
                let last_index = str.rfind(s).unwrap();
                char_to_last_index.insert(s, last_index);
            }

            char_to_last_index
        };

        let mut start_index = 0;
        loop {
            let parts_size = Self::solution(str, start_index, &char_to_last_index);
            result.push(i32::try_from(parts_size).unwrap());
            start_index += parts_size;

            if start_index == str.len() {
                break;
            }
        }

        result
    }

    fn solution(str: &str, start_index: usize, char_to_last_index: &HashMap<&str, usize>) -> usize {
        let initial_target = &str[start_index..=start_index];
        let mut last_index = char_to_last_index.get(initial_target).unwrap();

        if start_index == *last_index {
            // return the parts "size"
            return 1;
        }

        loop {
            let partial_str = &str[start_index..=*last_index];
            let partial_strs = partial_str
                .split("")
                .filter(|&s| !s.is_empty())
                .collect::<Vec<&str>>();
            let max_char = partial_strs
                .iter()
                .max_by(|&a, &b| {
                    let a_index = char_to_last_index.get(*a).unwrap();
                    let b_index = char_to_last_index.get(*b).unwrap();
                    a_index.cmp(b_index)
                })
                .unwrap();
            let max_pos = char_to_last_index.get(*max_char).unwrap();

            if max_pos == last_index {
                break;
            }

            last_index = &max_pos;
        }

        last_index - start_index + 1
    }
}

#[test]
fn example1() {
    assert_eq!(
        Solution::partition_labels("ababcbacadefegdehijhklij".into()),
        vec![9, 7, 8]
    );
}

#[test]
fn example2() {
    assert_eq!(
        Solution::partition_labels("qiejxqfnqceocmy".into()),
        vec![13, 1, 1]
    );
}
