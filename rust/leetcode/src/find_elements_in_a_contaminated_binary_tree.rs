// https://leetcode.com/problems/find-elements-in-a-contaminated-binary-tree/

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

// Definition for a binary tree node.
#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}

impl TreeNode {
    #[allow(dead_code)]
    #[inline]
    pub fn new(val: i32) -> Self {
        TreeNode {
            val,
            left: None,
            right: None,
        }
    }
}

#[derive(Debug)]
struct FindElements {
    vals: HashSet<i32>,
}

/**
 * `&self` means the method takes an immutable reference.
 * If you need a mutable reference, change it to `&mut self` instead.
 */
impl FindElements {
    fn new(mut root: Option<Rc<RefCell<TreeNode>>>) -> Self {
        let mut vals = HashSet::new();

        if let Some(mut root) = root.as_mut() {
            Self::initialize_tree(&mut root, 0, &mut vals);
        }

        // println!("{:?}", root);

        FindElements { vals }
    }

    fn initialize_tree(node: &mut Rc<RefCell<TreeNode>>, val: i32, vals: &mut HashSet<i32>) {
        node.borrow_mut().val = val;
        vals.insert(val);

        if let Some(mut left) = node.borrow_mut().left.as_mut() {
            Self::initialize_tree(&mut left, 2 * val + 1, vals);
        }

        if let Some(mut right) = node.borrow_mut().right.as_mut() {
            Self::initialize_tree(&mut right, 2 * val + 2, vals);
        }
    }

    fn find(&self, target: i32) -> bool {
        self.vals.contains(&target)
    }
}

/**
 * Your FindElements object will be instantiated and called as such:
 * let obj = FindElements::new(root);
 * let ret_1: bool = obj.find(target);
 */

mod test {
    use super::*;

    #[test]
    fn test() {
        let t = new_tree_node(-1, None, Some(new_tree_node(-1, None, None)));
        let fe = FindElements::new(Some(t));
        assert!(!fe.find(1));
        assert!(fe.find(2));
    }

    fn new_tree_node(
        val: i32,
        left: Option<Rc<RefCell<TreeNode>>>,
        right: Option<Rc<RefCell<TreeNode>>>,
    ) -> Rc<RefCell<TreeNode>> {
        Rc::new(RefCell::new(TreeNode { val, left, right }))
    }
}
