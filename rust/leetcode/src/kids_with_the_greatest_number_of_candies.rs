// https://leetcode.com/problems/kids-with-the-greatest-number-of-candies/

struct Solution;

impl Solution {
    pub fn kids_with_candies(candies: Vec<i32>, extra_candies: i32) -> Vec<bool> {
        let greatest = {
            let mut c = candies.clone();
            c.sort();
            c.last().unwrap().clone()
        };

        let mut result = vec![];
        for c in candies {
            result.push(c + extra_candies >= greatest);
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![true,true,true,false,true],
        Solution::kids_with_candies(vec![2,3,5,1,3], 3)
    );
}
