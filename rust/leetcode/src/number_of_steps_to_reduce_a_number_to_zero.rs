// https://leetcode.com/problems/number-of-steps-to-reduce-a-number-to-zero/

struct Solution;

impl Solution {
    pub fn number_of_steps(num: i32) -> i32 {
        assert!(num >= 0);

        let mut n = num;
        let mut result = 0;

        loop {
            if n == 0 {
                break;
            }
            result += 1;

            if n % 2 == 0 {
                n /= 2;
            } else {
                n -= 1;
            }
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(Solution::number_of_steps(14), 6);
}
