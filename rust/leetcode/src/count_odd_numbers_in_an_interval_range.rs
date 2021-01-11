// https://leetcode.com/problems/count-odd-numbers-in-an-interval-range/

struct Solution;

impl Solution {
    pub fn count_odds(low: i32, high: i32) -> i32 {
        assert!(low <= high);

        let mut count = 0;
        for n in low..=high {
            if n % 2 == 1 {
                count += 1;
            }
        }

        count
    }
}

#[test]
fn test() {
    assert_eq!(3, Solution::count_odds(3, 7));
    assert_eq!(1, Solution::count_odds(8, 10));
}
