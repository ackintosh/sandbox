// https://leetcode.com/problems/xor-operation-in-an-array/

struct Solution;

impl Solution {
    pub fn xor_operation(n: i32, start: i32) -> i32 {
        let mut nums = vec![];
        for i in 0..n {
            nums.push(start.checked_add(2_i32.checked_mul(i).unwrap()).unwrap());
        }

        let mut iter = nums.iter();
        let mut result = *iter.next().unwrap();

        for n in iter {
            result ^= n;
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(Solution::xor_operation(5, 0), 8);
}
