// https://leetcode.com/problems/count-number-of-distinct-integers-after-reverse-operations/description/

use std::collections::HashSet;

struct Solution;

impl Solution {
    pub fn count_distinct_integers(nums: Vec<i32>) -> i32 {
        let mut set = HashSet::new();

        for n in nums {
            set.insert(rev(n));
            set.insert(n);
        }

        set.len() as i32
    }
}

fn rev(mut n: i32) -> i32 {
    let mut rev = 0;

    while n > 0 {
        rev = (rev * 10) + (n % 10);
        n = n / 10;
    }

    rev
}

#[test]
fn test_rev() {
    assert_eq!(13, rev(31));
    assert_eq!(1, rev(10));
    assert_eq!(1, rev(1));
}

#[test]
fn test() {
    assert_eq!(
        6,
        Solution::count_distinct_integers(vec![1, 13, 10, 12, 31])
    );
    assert_eq!(1, Solution::count_distinct_integers(vec![2, 2, 2]));
}
