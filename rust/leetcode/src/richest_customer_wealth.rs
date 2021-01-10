// https://leetcode.com/problems/richest-customer-wealth/

struct Solution;

impl Solution {
    pub fn maximum_wealth(accounts: Vec<Vec<i32>>) -> i32 {
        let mut wealth_per_account = accounts
            .iter()
            .map(|banks| {
                banks.iter().sum::<i32>()
            })
            .collect::<Vec<i32>>();
        wealth_per_account.sort();
        wealth_per_account.last().unwrap().clone()
    }
}

#[test]
fn test() {
    let maximum_wealth = Solution::maximum_wealth(vec![vec![1, 2, 3], vec![3, 2, 1]]);
    assert_eq!(maximum_wealth, 6);
}
