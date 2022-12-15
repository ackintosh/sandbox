// https://leetcode.com/problems/count-good-nodes-in-binary-tree/

struct Solution;

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
use std::cell::RefCell;
use std::rc::Rc;
impl Solution {
    pub fn good_nodes(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
        let mut answer = 0;
        Self::dfs(root, &mut answer, vec![]);
        answer
    }

    fn dfs(maybe_node: Option<Rc<RefCell<TreeNode>>>, answer: &mut i32, mut path: Vec<i32>) {
        if let Some(node) = maybe_node {
            let v = node.borrow().val;
            if path.iter().find(|&p| p > &v).is_none() {
                *answer += 1;
            }

            path.push(v);

            let r = node.borrow().right.clone();
            Self::dfs(r, answer, path.clone());
            let l = node.borrow().left.clone();
            Self::dfs(l, answer, path.clone());
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
            3,
            new_tree_node(1, new_tree_node(3, None, None), None),
            new_tree_node(
                4,
                new_tree_node(1, None, None),
                new_tree_node(5, None, None),
            ),
        );
        let answer = Solution::good_nodes(root);
        println!("{:?}", answer);
    }
}
