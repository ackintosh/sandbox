// https://leetcode.com/problems/maximum-number-of-coins-you-can-get/

struct Solution;

impl Solution {
    pub fn max_coins(mut piles: Vec<i32>) -> i32 {
        piles.sort_unstable();

        let mut result = 0;

        while !piles.is_empty() {
            let _alice = piles.remove(piles.len() - 1);
            let mine = piles.remove(piles.len() - 1);
            let _bob = piles.remove(0);

            result += mine;
        }

        result
    }
}

#[test]
fn example1() {
    assert_eq!(Solution::max_coins(vec![2, 4, 1, 2, 7, 8]), 9);
}

#[test]
fn example2() {
    assert_eq!(Solution::max_coins(vec![2, 4, 5]), 4);
}

#[test]
fn example3() {
    assert_eq!(Solution::max_coins(vec![9, 8, 7, 6, 5, 1, 2, 3, 4]), 18);
}
