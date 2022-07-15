// https://leetcode.com/problems/partition-array-according-to-given-pivot/

use std::cmp::Ordering;

struct Solution;

impl Solution {
    pub fn pivot_array(nums: Vec<i32>, pivot: i32) -> Vec<i32> {
        let mut less = vec![];
        let mut equal = vec![];
        let mut greater = vec![];

        for n in nums {
            match n.cmp(&pivot) {
                Ordering::Less => less.push(n),
                Ordering::Equal => equal.push(n),
                Ordering::Greater => greater.push(n),
            }
        }

        less.append(&mut equal);
        less.append(&mut greater);
        less
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![9, 5, 3, 10, 10, 12, 14],
        Solution::pivot_array(vec![9, 12, 5, 10, 14, 3, 10], 10)
    );
}
