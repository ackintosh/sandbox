// https://leetcode.com/problems/sum-of-nodes-with-even-valued-grandparent/

// Definition for a binary tree node.
#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}

// impl TreeNode {
//     #[inline]
//     pub fn new(val: i32) -> Self {
//         TreeNode {
//             val,
//             left: None,
//             right: None,
//         }
//     }
// }
use std::borrow::Borrow;
use std::cell::RefCell;
use std::rc::Rc;

struct Solution;

impl Solution {
    pub fn sum_even_grandparent(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
        Self::solution(root, 1, 1)
    }

    fn solution(
        node: Option<Rc<RefCell<TreeNode>>>,
        parent_val: i32,
        grand_parent_val: i32,
    ) -> i32 {
        if let Some(node) = node {
            let mut result = 0;
            let node_refcell: &RefCell<TreeNode> = node.borrow();
            let node_val = node_refcell.borrow().val;

            if grand_parent_val % 2 == 0 {
                result += node_val;
            }

            result += Self::solution(node_refcell.borrow().left.clone(), node_val, parent_val);
            result += Self::solution(node_refcell.borrow().right.clone(), node_val, parent_val);
            return result;
        }
        0
    }
}

mod test {
    use super::*;

    #[test]
    fn test() {
        // Input: root = [6,7,8,2,7,1,3,9,null,1,4,null,null,null,5]
        // Output: 18
        let root = TreeNode {
            val: 6,
            left: Some(new_tree_node(
                7,
                Some(new_tree_node(2, Some(new_tree_node(9, None, None)), None)),
                Some(new_tree_node(
                    7,
                    Some(new_tree_node(1, None, None)),
                    Some(new_tree_node(4, None, None)),
                )),
            )),
            right: Some(new_tree_node(
                8,
                Some(new_tree_node(1, None, None)),
                Some(new_tree_node(3, None, Some(new_tree_node(5, None, None)))),
            )),
        };
        println!("{:?}", root);

        assert_eq!(
            Solution::sum_even_grandparent(Some(Rc::new(RefCell::new(root)))),
            18
        );
    }

    fn new_tree_node(
        val: i32,
        left: Option<Rc<RefCell<TreeNode>>>,
        right: Option<Rc<RefCell<TreeNode>>>,
    ) -> Rc<RefCell<TreeNode>> {
        Rc::new(RefCell::new(TreeNode { val, left, right }))
    }
}
