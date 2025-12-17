// https://leetcode.com/problems/distribute-coins-in-binary-tree/description/
struct Solution;

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
use std::rc::Rc;
impl Solution {
    pub fn distribute_coins(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
        let mut answer = 0;

        let _ = Self::dfs(&root, &mut answer);

        answer
    }

    fn dfs(node: &Option<Rc<RefCell<TreeNode>>>, answer: &mut i32) -> i32 {
        if let Some(node) = node.as_ref() {
            let l = Self::dfs(&node.borrow().left, answer);
            let r = Self::dfs(&node.borrow().right, answer);
            *answer += l.abs() + r.abs();
            node.borrow().val + l + r - 1
        } else {
            0
        }
    }
}

#[test]
fn test() {
    let node = TreeNode {
        val: 3,
        left: Some(Rc::new(RefCell::new(TreeNode {
            val: 0,
            left: None,
            right: None,
        }))),
        right: Some(Rc::new(RefCell::new(TreeNode {
            val: 0,
            left: None,
            right: None,
        }))),
    };

    println!(
        "{}",
        Solution::distribute_coins(Some(Rc::new(RefCell::new(node))))
    );
}
