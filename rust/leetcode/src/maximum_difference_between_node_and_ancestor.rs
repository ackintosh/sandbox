// https://leetcode.com/problems/maximum-difference-between-node-and-ancestor/

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
    // https://leetcode.com/problems/maximum-difference-between-node-and-ancestor/solutions/274610/java-c-python-top-down/?orderBy=most_votes
    pub fn max_ancestor_diff(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
        Self::dfs(&root, i32::MAX, i32::MIN)
    }

    fn dfs(root: &Option<Rc<RefCell<TreeNode>>>, min: i32, max: i32) -> i32 {
        if let Some(node) = root.as_ref() {
            let mn = min.min(node.as_ref().borrow().val);
            let mx = max.max(node.as_ref().borrow().val);

            let diff1 = Self::dfs(&node.as_ref().borrow().left, mn, mx);
            let diff2 = Self::dfs(&node.as_ref().borrow().right, mn, mx);
            diff1.max(diff2)
        } else {
            max - min
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
            8,
            new_tree_node(
                3,
                new_tree_node(1, None, None),
                new_tree_node(
                    6,
                    new_tree_node(4, None, None),
                    new_tree_node(7, None, None),
                ),
            ),
            new_tree_node(
                10,
                None,
                new_tree_node(14, new_tree_node(13, None, None), None),
            ),
        );
        let answer = Solution::max_ancestor_diff(root);
        println!("{:?}", answer);
    }
}
