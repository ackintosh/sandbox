// https://leetcode.com/problems/maximum-number-of-words-found-in-sentences/

struct Solution;

impl Solution {
    pub fn most_words_found(sentences: Vec<String>) -> i32 {
        sentences.iter().fold(0, |max, sentence| {
            let len = sentence.split(' ').collect::<Vec<_>>().len();
            max.max(len as i32)
        })
    }
}

#[test]
fn test() {
    let input = vec![
        "alice and bob love leetcode".to_owned(),
        "i think so too".to_owned(),
        "this is great thanks very much".to_owned(),
    ];
    assert_eq!(6, Solution::most_words_found(input));
    let input = vec![
        "please wait".to_owned(),
        "continue to fight".to_owned(),
        "continue to win".to_owned(),
    ];
    assert_eq!(3, Solution::most_words_found(input));
}
