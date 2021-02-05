// https://leetcode.com/problems/binary-search-tree-to-greater-sum-tree/

struct Solution;

// Definition for a binary tree node.
#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}
//
// impl TreeNode {
//   #[inline]
//   pub fn new(val: i32) -> Self {
//     TreeNode {
//       val,
//       left: None,
//       right: None
//     }
//   }
// }
use std::cell::RefCell;
use std::rc::Rc;

impl Solution {
    pub fn bst_to_gst(root: Option<Rc<RefCell<TreeNode>>>) -> Option<Rc<RefCell<TreeNode>>> {
        let mut sum = 0;
        Self::solution(&root, &mut sum);
        root
    }

    fn solution(node: &Option<Rc<RefCell<TreeNode>>>, sum: &mut i32) {
        match node {
            Some(node) => {
                let mut node_refmut = node.borrow_mut();
                Self::solution(&node_refmut.right, sum);
                *sum += node_refmut.val;
                node_refmut.val = *sum;
                Self::solution(&node_refmut.left, sum);
            }
            None => {}
        }
    }
}

mod test {
    use super::*;

    #[test]
    fn test_0() {
        // Input: root = [0,null,1]
        // Output: [1,null,1]
        let bst = TreeNode {
            val: 0,
            left: None,
            right: new_tree_node(1, None, None),
        };

        let gst = Solution::bst_to_gst(Some(Rc::new(RefCell::new(bst))));
        println!("gst: {:?}", gst);
    }

    #[test]
    fn test_1() {
        // Input: root = [3,2,4,1]
        // Output: [7,9,4,10]
        let bst = TreeNode {
            val: 3,
            left: new_tree_node(2, new_tree_node(1, None, None), None),
            right: new_tree_node(4, None, None),
        };

        let gst = Solution::bst_to_gst(Some(Rc::new(RefCell::new(bst))));
        println!("gst: {:?}", gst);
    }

    #[test]
    fn test() {
        // Input: root = [4,1,6,0,2,5,7,null,null,null,3,null,null,null,8]
        // Output: [30,36,21,36,35,26,15,null,null,null,33,null,null,null,8]
        let bst = TreeNode {
            val: 4,
            left: new_tree_node(
                1,
                new_tree_node(0, None, None),
                new_tree_node(2, None, new_tree_node(3, None, None)),
            ),
            right: new_tree_node(
                6,
                new_tree_node(5, None, None),
                new_tree_node(7, None, new_tree_node(8, None, None)),
            ),
        };
        println!("bst: {:?}", bst);

        let gst = Solution::bst_to_gst(Some(Rc::new(RefCell::new(bst))));
        println!("root: {:?}", gst);
    }

    fn new_tree_node(
        val: i32,
        left: Option<Rc<RefCell<TreeNode>>>,
        right: Option<Rc<RefCell<TreeNode>>>,
    ) -> Option<Rc<RefCell<TreeNode>>> {
        Some(Rc::new(RefCell::new(TreeNode { val, left, right })))
    }
}
