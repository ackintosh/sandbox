// https://leetcode.com/problems/all-possible-full-binary-trees/

// Definition for a binary tree node.
#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}

impl TreeNode {
    #[inline]
    pub fn new(val: i32) -> Self {
        TreeNode {
            val,
            left: None,
            right: None,
        }
    }
}

struct Solution;

use std::cell::RefCell;
use std::rc::Rc;

// https://leetcode.com/problems/all-possible-full-binary-trees/discuss/216853/Java%3A-Easy-with-Examples

impl Solution {
    pub fn all_possible_fbt(n: i32) -> Vec<Option<Rc<RefCell<TreeNode>>>> {
        // assert_eq!(n % 2, 1);

        let mut result = vec![];

        // 1. if N = 3 , the number of nodes combination are as follows
        //       left    root    right
        //        1       1        1
        // --------------N = 3, res = 1----------

        // 2. if N = 5 , the number of nodes combination are as follows
        //       left    root    right
        //        1       1        3 (recursion)
        //        3       1        1
        //   --------------N = 5, res = 1 + 1 = 2----------

        // 3. if N = 7 , the number of nodes combination are as follows
        //       left    root    right
        //        1       1        5 (recursion)
        //        3       1        3
        //        5       1        1
        //   --------------N = 7, res = 2 + 1 + 2 = 5----------

        // 4. in order to make full binary tree, the node number must increase by 2

        if n == 1 {
            return vec![Some(Rc::new(RefCell::new(TreeNode::new(0))))];
        } else {
            for i in (1..n).step_by(2) {
                let left_trees = Self::all_possible_fbt(i);
                let right_trees = Self::all_possible_fbt(n - i - 1);

                for left in &left_trees {
                    for right in &right_trees {
                        let mut root = TreeNode::new(0);
                        root.left = left.clone();
                        root.right = right.clone();

                        result.push(Some(Rc::new(RefCell::new(root))));
                    }
                }
            }
        }

        result
    }
}

#[test]
fn test() {
    let result = Solution::all_possible_fbt(3);
    println!("{:?}", result);

    let result = Solution::all_possible_fbt(7);
    println!("{:?}", result);
}
