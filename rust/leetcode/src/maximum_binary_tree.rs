// https://leetcode.com/problems/maximum-binary-tree/

struct Solution;

// Definition for a binary tree node.
#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}
//
// impl TreeNode {
//   #[inline]
//   pub fn new(val: i32) -> Self {
//     TreeNode {
//       val,
//       left: None,
//       right: None
//     }
//   }
// }
use std::cell::RefCell;
use std::rc::Rc;
impl Solution {
    pub fn construct_maximum_binary_tree(nums: Vec<i32>) -> Option<Rc<RefCell<TreeNode>>> {
        Self::solution(nums.as_slice())
    }

    fn solution(nums: &[i32]) -> Option<Rc<RefCell<TreeNode>>> {
        if nums.is_empty() {
            return None;
        }

        let (max_num, max_index) = {
            let mut max_num = 0;
            let mut max_index = 0;
            nums.iter().enumerate().for_each(|(index, &n)| {
                if max_num < n {
                    max_num = n;
                    max_index = index;
                }
            });
            (max_num, max_index)
        };

        let (left, right) = {
            let (left, right_includes_max) = nums.split_at(max_index);

            // rightは最大値を除いたスライス(インデックスが1以降)を返す
            (left, &right_includes_max[1..])
        };

        Some(Rc::new(RefCell::new(TreeNode {
            val: max_num,
            left: Self::solution(left),
            right: Self::solution(right),
        })))
    }
}

mod test {
    use super::*;

    #[test]
    fn example2() {
        // Input: nums = [3,2,1]
        // Output: [3,null,2,null,1]
        let mbt = Solution::construct_maximum_binary_tree(vec![3, 2, 1]);
        println!("mbt: {:?}", mbt);
    }
}
