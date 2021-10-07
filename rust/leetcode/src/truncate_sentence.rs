// https://leetcode.com/problems/truncate-sentence/
use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn truncate_sentence(s: String, k: i32) -> String {
        let sc = s.split(' ').collect::<Vec<&str>>();
        sc[0..usize::try_from(k).unwrap()].join(" ")
    }
}

mod test {
    use crate::truncate_sentence::Solution;

    #[test]
    fn example1() {
        assert_eq!(
            "Hello how are you".to_owned(),
            Solution::truncate_sentence("Hello how are you Contestant".to_owned(), 4)
        );
    }
}
