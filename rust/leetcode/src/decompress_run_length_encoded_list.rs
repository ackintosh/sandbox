// https://leetcode.com/problems/decompress-run-length-encoded-list/

struct Solution;

impl Solution {
    pub fn decompress_rl_elist(nums: Vec<i32>) -> Vec<i32> {
        let until = nums.len() / 2;
        let mut result = vec![];

        for i in 0..until {
            let freq = nums.get(2 * i).unwrap();
            let val = nums.get(2 * i + 1).unwrap();

            for _ in 0..*freq {
                result.push(*val);
            }
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        Solution::decompress_rl_elist(vec![1, 2, 3, 4]),
        vec![2, 4, 4, 4]
    );
}
