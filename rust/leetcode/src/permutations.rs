// https://leetcode.com/problems/permutations/

struct Solution;

impl Solution {
    pub fn permute(nums: Vec<i32>) -> Vec<Vec<i32>> {
        let mut answer = vec![];

        Self::p(nums, vec![], &mut answer);

        answer
    }

    fn p(nums: Vec<i32>, path: Vec<i32>, answer: &mut Vec<Vec<i32>>) {
        for (i, n) in nums.iter().enumerate() {
            let mut my_path = path.clone();
            my_path.push(*n);

            let mut my_nums = nums.clone();
            my_nums.remove(i);

            if my_nums.len() == 0 {
                answer.push(my_path);
            } else {
                Self::p(my_nums, my_path, answer);
            }
        }
    }
}

#[test]
fn test() {
    println!("{:?}", Solution::permute(vec![1, 2, 3]));
}
