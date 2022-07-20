// https://leetcode.com/problems/construct-binary-search-tree-from-preorder-traversal/

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

use std::cell::RefCell;
use std::rc::Rc;

struct Solution;

impl Solution {
    pub fn bst_from_preorder(preorder: Vec<i32>) -> Option<Rc<RefCell<TreeNode>>> {
        let mut result = None;

        for n in preorder {
            Self::append(&mut result, n);
        }

        result
    }

    fn append(node: &mut Option<Rc<RefCell<TreeNode>>>, val: i32) {
        match node {
            Some(tree_node) => {
                if tree_node.borrow().val > val {
                    Self::append(&mut tree_node.borrow_mut().left, val);
                } else {
                    Self::append(&mut tree_node.borrow_mut().right, val);
                }
            }
            None => {
                *node = Some(Rc::new(RefCell::new(TreeNode::new(val))));
            }
        }
    }
}

#[test]
fn test() {
    let result = Solution::bst_from_preorder(vec![8, 5, 1, 7, 10, 12]);
    println!("{:?}", result);
}
