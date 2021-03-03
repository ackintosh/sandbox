// https://leetcode.com/problems/all-elements-in-two-binary-search-trees/

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

struct Solution;

use std::borrow::Borrow;
use std::cell::RefCell;
use std::rc::Rc;

impl Solution {
    pub fn get_all_elements(
        root1: Option<Rc<RefCell<TreeNode>>>,
        root2: Option<Rc<RefCell<TreeNode>>>,
    ) -> Vec<i32> {
        let mut elements1 = Self::traverse_tree(&root1);
        let mut elements2 = Self::traverse_tree(&root2);

        elements1.append(&mut elements2);
        elements1.sort_unstable();
        elements1
    }

    fn traverse_tree(tree: &Option<Rc<RefCell<TreeNode>>>) -> Vec<i32> {
        match tree {
            Some(tree) => {
                let mut ret = vec![];
                let tree_r: &RefCell<TreeNode> = tree.borrow();

                ret.push(tree_r.borrow().val);
                ret.append(&mut Self::traverse_tree(&tree_r.borrow().left));
                ret.append(&mut Self::traverse_tree(&tree_r.borrow().right));
                ret
            }
            None => vec![],
        }
    }
}

mod test {
    use super::*;

    #[test]
    fn example1() {
        // Input: root1 = [2,1,4], root2 = [1,0,3]
        // Output: [0,1,1,2,3,4]
        let root1 = TreeNode {
            val: 2,
            left: new_tree_node(1, None, None),
            right: new_tree_node(4, None, None),
        };
        let root2 = TreeNode {
            val: 1,
            left: new_tree_node(0, None, None),
            right: new_tree_node(3, None, None),
        };

        let elements = Solution::get_all_elements(
            Some(Rc::new(RefCell::new(root1))),
            Some(Rc::new(RefCell::new(root2))),
        );
        assert_eq!(elements, vec![0, 1, 1, 2, 3, 4]);
    }

    #[allow(clippy::unnecessary_wraps)]
    fn new_tree_node(
        val: i32,
        left: Option<Rc<RefCell<TreeNode>>>,
        right: Option<Rc<RefCell<TreeNode>>>,
    ) -> Option<Rc<RefCell<TreeNode>>> {
        Some(Rc::new(RefCell::new(TreeNode { val, left, right })))
    }
}
