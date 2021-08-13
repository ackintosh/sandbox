// https://leetcode.com/problems/maximum-product-difference-between-two-pairs/

struct Solution;

impl Solution {
    pub fn max_product_difference(nums: Vec<i32>) -> i32 {
        let mut sorted = nums;
        sorted.sort_unstable();

        sorted[sorted.len() - 1] * sorted[sorted.len() - 2] - sorted[0] * sorted[1]
    }
}

mod test {
    use super::Solution;

    #[test]
    fn example1() {
        assert_eq!(34, Solution::max_product_difference(vec![5, 6, 2, 7, 4]));
    }

    #[test]
    fn example2() {
        assert_eq!(
            64,
            Solution::max_product_difference(vec![4, 2, 5, 9, 7, 4, 8])
        );
    }
}
