// https://leetcode.com/problems/balance-a-binary-search-tree/

// https://www.youtube.com/watch?v=uFsLlmMz9Yg
// https://www.youtube.com/watch?v=sXGuyZgNKl8

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

type Node = Rc<RefCell<TreeNode>>;

impl Solution {
    pub fn balance_bst(root: Option<Node>) -> Option<Node> {
        let in_order: Rc<RefCell<Vec<i32>>> = Rc::new(RefCell::new(vec![]));

        Self::flatten_values(root.clone(), in_order.clone());
        println!("{:?}", in_order);

        let end = in_order.borrow().len() - 1;
        Self::build_tree(in_order, 0, end)
    }

    fn flatten_values(node: Option<Node>, in_order: Rc<RefCell<Vec<i32>>>) {
        if let Some(n) = node {
            Self::flatten_values(n.borrow().left.clone(), in_order.clone());
            in_order.borrow_mut().push(n.borrow().val);
            Self::flatten_values(n.borrow().right.clone(), in_order.clone());
        };
    }

    fn build_tree(in_order: Rc<RefCell<Vec<i32>>>, start: usize, end: usize) -> Option<Node> {
        println!("[build_tree] start: {}, end: {}", start, end);
        if start > end {
            println!("[build_tree({}, {})] return", start, end);
            return None;
        }

        let mid = start + ((end - start) / 2);
        println!("[build_tree({}, {})] mid: {}", start, end, mid);

        let mut node = TreeNode::new(
            *in_order
                .borrow()
                .get(mid)
                .expect("should have the mid index"),
        );
        if let Some(e) = mid.checked_sub(1) {
            node.left = Self::build_tree(in_order.clone(), start, e);
        }
        if let Some(s) = mid.checked_add(1) {
            node.right = Self::build_tree(in_order.clone(), s, end);
        }

        Some(Rc::new(RefCell::new(node)))
    }
}

#[cfg(test)]
mod test {
    use crate::balance_a_binary_search_tree::{Node, Solution, TreeNode};
    use std::cell::RefCell;
    use std::rc::Rc;

    fn new_tree_node(val: i32, left: Option<Node>, right: Option<Node>) -> Option<Node> {
        Some(Rc::new(RefCell::new(TreeNode { val, left, right })))
    }

    #[test]
    fn example1() {
        let root = new_tree_node(
            1,
            None,
            new_tree_node(
                2,
                None,
                new_tree_node(3, None, new_tree_node(4, None, None)),
            ),
        );
        let result = Solution::balance_bst(root);
        println!("result: {:?}", result);
    }

    #[test]
    fn example2() {
        let root = new_tree_node(
            2,
            new_tree_node(1, None, None),
            new_tree_node(3, None, None),
        );
        let result = Solution::balance_bst(root);
        println!("result: {:?}", result);
    }
}
