// https://leetcode.com/problems/decode-xored-array/

struct Solution;

impl Solution {
    pub fn decode(encoded: Vec<i32>, first: i32) -> Vec<i32> {
        let mut result = vec![first];

        for e in encoded {
            let n = result.last().unwrap() ^ e;
            result.push(n);
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(Solution::decode(vec![1, 2, 3], 1), vec![1, 0, 2, 1]);
}
