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
        if root.is_none() {
            return 0;
        }

        let root_n = Self::sum_grandson(root.as_ref());

        let root_node = root.unwrap();
        let root_node_refcell: &RefCell<TreeNode> = root_node.borrow();

        let left_n = root_node_refcell
            .borrow()
            .left
            .as_ref()
            .map_or(0, |left| Self::sum_even_grandparent(Some(left.clone())));
        let right_n = root_node_refcell
            .borrow()
            .right
            .as_ref()
            .map_or(0, |right| Self::sum_even_grandparent(Some(right.clone())));

        root_n
            .checked_add(left_n)
            .unwrap()
            .checked_add(right_n)
            .unwrap()
    }

    fn sum_grandson(root: Option<&Rc<RefCell<TreeNode>>>) -> i32 {
        if root.is_none() {
            return 0;
        }

        let root_rc = root.unwrap();

        let root_node: &RefCell<TreeNode> = root_rc.borrow();

        if root_node.borrow().val % 2 != 0 {
            return 0;
        }

        let left_val = root_node.borrow().left.as_ref().map_or(0, |left| {
            let left_node: &RefCell<TreeNode> = left.borrow();
            let leftleft_val = left_node.borrow().left.as_ref().map_or(0, |leftleft| {
                let leftleft_node: &RefCell<TreeNode> = leftleft.borrow();
                leftleft_node.borrow().val
            });
            let leftright_val = left_node.borrow().right.as_ref().map_or(0, |leftright| {
                let leftright_node: &RefCell<TreeNode> = leftright.borrow();
                leftright_node.borrow().val
            });
            leftleft_val.checked_add(leftright_val).unwrap()
        });

        let right_val = root_node.borrow().right.as_ref().map_or(0, |right| {
            let right_node: &RefCell<TreeNode> = right.borrow();
            let rightleft_val = right_node.borrow().left.as_ref().map_or(0, |rightleft| {
                let rightleft_node: &RefCell<TreeNode> = rightleft.borrow();
                rightleft_node.borrow().val
            });
            let rightright_val = right_node.borrow().right.as_ref().map_or(0, |rightright| {
                let rightright_node: &RefCell<TreeNode> = rightright.borrow();
                rightright_node.borrow().val
            });
            rightleft_val.checked_add(rightright_val).unwrap()
        });

        left_val.checked_add(right_val).unwrap()
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
