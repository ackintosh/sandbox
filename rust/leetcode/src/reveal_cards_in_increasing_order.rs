// https://leetcode.com/problems/reveal-cards-in-increasing-order/

struct Solution;

impl Solution {
    pub fn deck_revealed_increasing(mut deck: Vec<i32>) -> Vec<i32> {
        deck.sort();
        let mut result = vec![];

        while !deck.is_empty() {
            if !result.is_empty() {
                let n = result.pop().unwrap();
                result.insert(0, n);
            }
            let n = deck.pop().unwrap();
            result.insert(0, n);
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![2, 13, 3, 11, 5, 17, 7],
        Solution::deck_revealed_increasing(vec![17, 13, 11, 2, 3, 5, 7])
    );
    assert_eq!(
        vec![1, 1000],
        Solution::deck_revealed_increasing(vec![1, 1000])
    );
}
