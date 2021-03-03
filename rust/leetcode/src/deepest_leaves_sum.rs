// https://leetcode.com/problems/deepest-leaves-sum/

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

struct Solution;

use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

impl Solution {
    pub fn deepest_leaves_sum(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
        let sums = Rc::new(RefCell::new(HashMap::new()));

        Self::solution(root, 0, Rc::clone(&sums));

        let sums_refcell: &RefCell<HashMap<u32, i32>> = sums.borrow();
        let sums_hashmap = sums_refcell.borrow();

        println!("sums_hashmap: {:?}", sums_hashmap);

        // 最下層のノードの合計値
        *sums_hashmap
            .iter()
            .max_by(|a, b| a.0.cmp(b.0))
            .map(|deepest_leaves_sum| deepest_leaves_sum.1)
            .unwrap()
    }

    fn solution(
        root: Option<Rc<RefCell<TreeNode>>>,
        depth: u32,
        sums: Rc<RefCell<HashMap<u32, i32>>>,
    ) {
        if root.is_none() {
            return;
        }

        let root_node = root.unwrap();
        let root_refcell: &RefCell<TreeNode> = root_node.borrow();

        let sum_refcell: &RefCell<HashMap<u32, i32>> = sums.borrow();
        let sum = {
            let hashmap = sum_refcell.borrow();
            let sum = hashmap.get(&depth).unwrap_or(&0);
            sum + root_refcell.borrow().val
        };
        sum_refcell.borrow_mut().insert(depth, sum);

        Self::solution(
            root_refcell.borrow().left.clone(),
            depth + 1,
            Rc::clone(&sums),
        );
        Self::solution(
            root_refcell.borrow().right.clone(),
            depth + 1,
            Rc::clone(&sums),
        );
    }
}

mod test {
    use super::*;

    #[test]
    fn test() {
        // Input: root = [1,2,3,4,5,null,6,7,null,null,null,null,8]
        // Output: 15
        let root = TreeNode {
            val: 1,
            left: new_tree_node(
                2,
                new_tree_node(4, new_tree_node(7, None, None), None),
                new_tree_node(5, None, None),
            ),
            right: new_tree_node(
                3,
                None,
                new_tree_node(6, None, new_tree_node(8, None, None)),
            ),
        };
        println!("{:?}", root);

        assert_eq!(
            Solution::deepest_leaves_sum(Some(Rc::new(RefCell::new(root)))),
            15
        );
    }

    #[test]
    fn test2() {
        // Input: [50,null,54,98,6,null,null,null,34]
        // Output: 34
        let root = TreeNode {
            val: 50,
            left: None,
            right: new_tree_node(
                54,
                new_tree_node(98, None, None),
                new_tree_node(6, None, new_tree_node(34, None, None)),
            ),
        };
        println!("{:?}", root);

        assert_eq!(
            Solution::deepest_leaves_sum(Some(Rc::new(RefCell::new(root)))),
            34
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
}
