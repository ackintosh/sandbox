// https://leetcode.com/problems/delete-leaves-with-a-given-value/

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

use std::borrow::BorrowMut;
use std::cell::RefCell;
use std::rc::Rc;

struct Solution;

impl Solution {
    pub fn remove_leaf_nodes(
        root: Option<Rc<RefCell<TreeNode>>>,
        target: i32,
    ) -> Option<Rc<RefCell<TreeNode>>> {
        Self::dfs(root.clone(), target)
    }

    fn dfs(
        mut maybe_node: Option<Rc<RefCell<TreeNode>>>,
        target: i32,
    ) -> Option<Rc<RefCell<TreeNode>>> {
        if let Some(mut node) = maybe_node {
            let n = node.borrow();
            let left = Self::dfs(n.left.clone(), target);
            let right = Self::dfs(n.right.clone(), target);

            if left.is_none() && right.is_none() && n.val == target {
                None
            } else {
                new_tree_node(n.val, left, right)
            }
        } else {
            maybe_node
        }
    }
}

#[allow(clippy::unnecessary_wraps)]
fn new_tree_node(
    val: i32,
    left: Option<Rc<RefCell<TreeNode>>>,
    right: Option<Rc<RefCell<TreeNode>>>,
) -> Option<Rc<RefCell<TreeNode>>> {
    Some(Rc::new(RefCell::new(TreeNode { val, left, right })))
}

mod test {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[allow(clippy::unnecessary_wraps)]
    fn new_tree_node(
        val: i32,
        left: Option<Rc<RefCell<TreeNode>>>,
        right: Option<Rc<RefCell<TreeNode>>>,
    ) -> Option<Rc<RefCell<TreeNode>>> {
        Some(Rc::new(RefCell::new(TreeNode { val, left, right })))
    }

    #[test]
    fn test() {
        let root = new_tree_node(
            1,
            new_tree_node(2, new_tree_node(2, None, None), None),
            new_tree_node(
                3,
                new_tree_node(2, None, None),
                new_tree_node(4, None, None),
            ),
        );
        let result = Solution::remove_leaf_nodes(root, 2);
        println!("{:?}", result);
    }
}
