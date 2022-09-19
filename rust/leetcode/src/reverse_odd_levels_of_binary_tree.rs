// https://leetcode.com/problems/reverse-odd-levels-of-binary-tree/
// Definition for a binary tree node.

#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}

impl TreeNode {
    #[inline]
    #[allow(dead_code)]
    pub fn new(val: i32) -> Self {
        TreeNode {
            val,
            left: None,
            right: None,
        }
    }
}

use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

struct Solution;

impl Solution {
    pub fn reverse_odd_levels(
        root: Option<Rc<RefCell<TreeNode>>>,
    ) -> Option<Rc<RefCell<TreeNode>>> {
        let mut queue = VecDeque::new();
        let mut level_to_values: HashMap<i32, Vec<i32>> = HashMap::new();

        if let Some(n) = root.as_ref() {
            queue.push_back((n.clone(), 0));

            let values = level_to_values.entry(0).or_insert(vec![]);
            if let Some(l) = n.borrow().left.as_ref() {
                values.push(l.borrow().val);
            }
            if let Some(r) = n.borrow().right.as_ref() {
                values.push(r.borrow().val);
            }
        }

        while let Some(n) = queue.pop_front() {
            let level = n.1;
            // println!("val: {}, level: {}", n.0.borrow().val, level);

            if level % 2 == 1 {
                let values = level_to_values.get_mut(&level).expect("should have values");
                n.0.borrow_mut().val = values.pop().expect("should have value");
            }

            let values = level_to_values.entry(level + 1).or_insert(vec![]);

            if let Some(l) = n.0.borrow().left.as_ref() {
                queue.push_back((l.clone(), level + 1));
                values.push(l.borrow().val);
            }
            if let Some(r) = n.0.borrow().right.as_ref() {
                queue.push_back((r.clone(), level + 1));
                values.push(r.borrow().val);
            }
        }

        root
    }
}

#[test]
fn test() {
    println!(
        "{:?}",
        Solution::reverse_odd_levels(new_tree_node(
            2,
            new_tree_node(
                3,
                new_tree_node(8, None, None),
                new_tree_node(13, None, None)
            ),
            new_tree_node(
                5,
                new_tree_node(21, None, None),
                new_tree_node(34, None, None)
            )
        ))
    );
}

#[allow(clippy::unnecessary_wraps)]
fn new_tree_node(
    val: i32,
    left: Option<Rc<RefCell<TreeNode>>>,
    right: Option<Rc<RefCell<TreeNode>>>,
) -> Option<Rc<RefCell<TreeNode>>> {
    Some(Rc::new(RefCell::new(TreeNode { val, left, right })))
}
