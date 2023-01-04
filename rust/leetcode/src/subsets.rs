// https://leetcode.com/problems/subsets/

struct Solution;

impl Solution {
    pub fn subsets(nums: Vec<i32>) -> Vec<Vec<i32>> {
        let mut answer = vec![];

        Self::dfs(&nums, &mut answer, vec![]);

        answer
    }

    //            *
    //          / | \
    //         1  2  3
    //       / |  |
    //     2   3   3
    //   /
    //  3
    fn dfs(nums: &[i32], answer: &mut Vec<Vec<i32>>, path: Vec<i32>) {
        answer.push(path.clone());

        for i in 0..nums.len() {
            let mut next_path = path.clone();
            next_path.push(nums[i]);
            Self::dfs(&nums[(i + 1)..nums.len()], answer, next_path);
        }
    }
}

#[test]
fn test() {
    let answer = Solution::subsets(vec![1, 2, 3]);
    println!("{:?}", answer);
    let answer = Solution::subsets(vec![0]);
    println!("{:?}", answer);
}
