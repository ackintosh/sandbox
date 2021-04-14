// https://leetcode.com/problems/find-n-unique-integers-sum-up-to-zero/

struct Solution;

impl Solution {
    pub fn sum_zero(n: i32) -> Vec<i32> {
        let mut result = vec![];
        if n % 2 == 1 {
            result.push(0);
        }

        for i in 0..(n / 2) {
            let ii = i + 1;
            result.push(ii);
            result.push(-ii);
        }

        result
    }
}

#[test]
fn example1() {
    let ret = Solution::sum_zero(5);
    assert!(!ret.is_empty());
    assert_eq!(0, ret.iter().sum::<i32>());
}
