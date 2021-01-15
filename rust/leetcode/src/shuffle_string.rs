// https://leetcode.com/problems/shuffle-string/
use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn restore_string(s: String, indices: Vec<i32>) -> String {
        assert_eq!(s.len(), indices.len());

        let mut data: Vec<(usize, &str)> = vec![];
        for (pos, str) in s.split("").filter(|&s| !s.is_empty()).enumerate() {
            let move_to = usize::try_from(indices[pos]).unwrap();
            data.push((move_to, str));
        }

        // indicesの昇順にソートする
        data.sort_by_key(|d| d.0);

        let mut result = String::new();
        for (_pos, str) in data.iter() {
            result.push_str(str);
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        "leetcode".to_owned(),
        Solution::restore_string("codeleet".to_owned(), vec![4, 5, 6, 7, 0, 2, 1, 3])
    );
}
