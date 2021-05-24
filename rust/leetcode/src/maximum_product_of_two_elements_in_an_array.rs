// https://leetcode.com/problems/maximum-product-of-two-elements-in-an-array/

struct Solution;

impl Solution {
    pub fn max_product(nums: Vec<i32>) -> i32 {
        let mut ns = nums;
        ns.sort_unstable();

        let a = ns.pop().unwrap() - 1;
        let b = ns.pop().unwrap() - 1;

        a * b
    }
}

#[test]
fn example1() {
    assert_eq!(12, Solution::max_product(vec![3, 4, 5, 2]));
}

#[test]
fn example2() {
    assert_eq!(16, Solution::max_product(vec![1, 5, 4, 5]));
}

#[test]
fn example3() {
    assert_eq!(12, Solution::max_product(vec![3, 7]));
}
