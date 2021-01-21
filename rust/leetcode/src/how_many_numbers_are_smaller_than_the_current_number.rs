// https://leetcode.com/problems/how-many-numbers-are-smaller-than-the-current-number/

struct Solution;

impl Solution {
    pub fn smaller_numbers_than_current(nums: Vec<i32>) -> Vec<i32> {
        let nums_sorted = {
            let mut cloned = nums.clone();
            cloned.sort_unstable();
            cloned
        };

        nums.iter().map(|n| {
            let mut count = 0;
            for nn in &nums_sorted {
                if nn < n {
                    count += 1;
                } else {
                    break;
                }
            }
            count
        }).collect()
    }
}

#[test]
fn test() {
    assert_eq!(Solution::smaller_numbers_than_current(vec![8,1,2,2,3]), vec![4,0,1,1,3]);
}
