// https://leetcode.com/problems/count-nodes-equal-to-average-of-subtree/

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

use std::cell::{Cell, RefCell};
use std::rc::Rc;

struct Solution;

impl Solution {
    pub fn average_of_subtree(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
        let result = Rc::new(Cell::new(0_i32));
        let _ = Self::size_and_sum_of_subtree(&root, result.clone());
        result.get()
    }

    fn size_and_sum_of_subtree(
        node: &Option<Rc<RefCell<TreeNode>>>,
        result: Rc<Cell<i32>>,
    ) -> (usize, i32) {
        match node {
            None => (0, 0),
            Some(ref node) => {
                let left = Self::size_and_sum_of_subtree(&node.borrow().left, result.clone());
                let right = Self::size_and_sum_of_subtree(&node.borrow().right, result.clone());
                let size = 1 + left.0 + right.0;
                let sum = (*node).borrow().val + left.1 + right.1;

                // println!(
                //     "val: {}, size: {}, sum: {}",
                //     (*node).borrow().val,
                //     size,
                //     sum
                // );

                let ave: i32 = sum / size as i32;
                if (*node).borrow().val == ave {
                    result.set(result.get() + 1);
                }

                (size, sum)
            }
        }
    }
}

#[test]
fn test() {
    let root = {
        let mut root = TreeNode::new(4);

        root.left = {
            let mut n = TreeNode::new(8);
            n.left = {
                let n = TreeNode::new(0);
                Some(Rc::new(RefCell::new(n)))
            };
            n.right = {
                let n = TreeNode::new(1);
                Some(Rc::new(RefCell::new(n)))
            };
            Some(Rc::new(RefCell::new(n)))
        };

        root.right = {
            let mut n = TreeNode::new(5);
            n.right = {
                let n = TreeNode::new(6);
                Some(Rc::new(RefCell::new(n)))
            };
            Some(Rc::new(RefCell::new(n)))
        };

        root
    };

    assert_eq!(
        5,
        Solution::average_of_subtree(Some(Rc::new(RefCell::new(root))))
    );
}
