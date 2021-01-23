// https://leetcode.com/problems/subtract-the-product-and-sum-of-digits-of-an-integer/

struct Solution;

impl Solution {
    pub fn subtract_product_and_sum(n: i32) -> i32 {
        let string = n.to_string();
        let mut product = 0;
        let mut sum = 0;

        for (i, s) in string.split("").filter(|s| !s.is_empty()).enumerate() {
            if i == 0 {
                product = s.parse().unwrap();
                sum = s.parse().unwrap();
                continue;
            }
            product *= s.parse::<i32>().unwrap();
            sum += s.parse::<i32>().unwrap();
        }

        product - sum
    }
}

#[test]
fn test() {
    assert_eq!(Solution::subtract_product_and_sum(234), 15);
}
