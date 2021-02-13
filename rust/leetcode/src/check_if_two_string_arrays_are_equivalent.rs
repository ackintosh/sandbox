// https://leetcode.com/problems/check-if-two-string-arrays-are-equivalent/

struct Solution;

impl Solution {
    pub fn array_strings_are_equal(word1: Vec<String>, word2: Vec<String>) -> bool {
        word1.concat() == word2.concat()
    }
}

#[test]
fn example1() {
    assert!(Solution::array_strings_are_equal(
        vec!["ab".into(), "c".into()],
        vec!["a".into(), "bc".into()]
    ));
}
