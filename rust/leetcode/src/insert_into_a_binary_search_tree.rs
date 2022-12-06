// https://leetcode.com/problems/insert-into-a-binary-search-tree/

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
use std::cmp::Ordering;
use std::rc::Rc;

impl Solution {
    pub fn insert_into_bst(
        root: Option<Rc<RefCell<TreeNode>>>,
        val: i32,
    ) -> Option<Rc<RefCell<TreeNode>>> {
        Self::dfs(root, val)
    }

    fn dfs(maybe_node: Option<Rc<RefCell<TreeNode>>>, val: i32) -> Option<Rc<RefCell<TreeNode>>> {
        if let Some(node) = maybe_node {
            let v = node.borrow().val;
            match val.cmp(&v) {
                Ordering::Less => {
                    let mut node_mut = node.borrow_mut();
                    if node_mut.left.is_none() {
                        node_mut.left = Some(Rc::new(RefCell::new(TreeNode::new(val))));
                    } else {
                        node_mut.left = Self::dfs(node_mut.left.clone(), val);
                    }
                    Some(node.clone())
                }
                Ordering::Equal => unreachable!(),
                Ordering::Greater => {
                    let mut node_mut = node.borrow_mut();
                    if node_mut.right.is_none() {
                        node_mut.right = Some(Rc::new(RefCell::new(TreeNode::new(val))));
                    } else {
                        node_mut.right = Self::dfs(node_mut.right.clone(), val);
                    }
                    Some(node.clone())
                }
            }
        } else {
            Some(Rc::new(RefCell::new(TreeNode::new(val))))
        }
    }
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
            4,
            new_tree_node(
                2,
                new_tree_node(1, None, None),
                new_tree_node(3, None, None),
            ),
            new_tree_node(7, None, None),
        );
        let result = Solution::insert_into_bst(root, 5);
        println!("{:?}", result);
    }

    #[test]
    fn test2() {
        let result = Solution::insert_into_bst(None, 5);
        println!("{:?}", result);
    }
}
