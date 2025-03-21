struct Solution;

use std::cell::{RefCell, RefMut};
use std::collections::HashMap;
use std::rc::Rc;

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

impl Solution {
    pub fn create_binary_tree(descriptions: Vec<Vec<i32>>) -> Option<Rc<RefCell<TreeNode>>> {
        let root = Self::find_root(&descriptions);
        // println!("root:{}", root.borrow().val);
        let map = Self::build_map(&descriptions);
        Self::append_children(&map, root.borrow_mut());
        Some(root)
    }

    fn find_root(desc: &Vec<Vec<i32>>) -> Rc<RefCell<TreeNode>> {
        let mut parent = desc.first().unwrap()[0];

        loop {
            let a = desc.iter().find(|node| node[1] == parent);
            match a {
                Some(node) => parent = node[0],
                None => break,
            }
        }

        Rc::new(RefCell::new(TreeNode::new(parent)))
    }

    fn build_map(desc: &Vec<Vec<i32>>) -> HashMap<i32, Vec<(i32, bool)>> {
        let mut map: HashMap<i32, Vec<(i32, bool)>> = HashMap::new();

        for d in desc {
            map.entry(d[0]).or_default().push((d[1], d[2] == 1));
        }

        map
    }

    fn append_children(map: &HashMap<i32, Vec<(i32, bool)>>, mut parent: RefMut<TreeNode>) {
        let (left, right) = Self::find_children(map, parent.val);
        // println!("append_children --> parent:{}, left:{:?}, right:{:?}", parent.val, left.as_ref().map(|i| i.val), right.as_ref().map(|i| i.val));
        if let Some(left) = left {
            let left = Rc::new(RefCell::new(left));
            Self::append_children(map, left.borrow_mut());
            parent.left = Some(left);
        }
        if let Some(right) = right {
            let right = Rc::new(RefCell::new(right));
            Self::append_children(map, right.borrow_mut());
            parent.right = Some(right);
        }
    }

    fn find_children(
        map: &HashMap<i32, Vec<(i32, bool)>>,
        parent_val: i32,
    ) -> (Option<TreeNode>, Option<TreeNode>) {
        if let Some(children) = map.get(&parent_val) {
            assert!(children.len() <= 2);

            let mut left = None;
            let mut right = None;
            for child in children {
                if child.1 {
                    left = Some(TreeNode::new(child.0));
                } else {
                    right = Some(TreeNode::new(child.0));
                }
            }

            (left, right)
        } else {
            (None, None)
        }
    }
}

#[test]
fn example1() {
    let answer = Solution::create_binary_tree(vec![
        vec![20, 15, 1],
        vec![20, 17, 0],
        vec![50, 20, 1],
        vec![50, 80, 0],
        vec![80, 19, 1],
    ]);
    println!("{answer:?}");
}

#[test]
fn example2() {
    let answer = Solution::create_binary_tree(vec![vec![1, 2, 1], vec![2, 3, 0], vec![3, 4, 1]]);
    println!("{answer:?}");
}

#[test]
fn example3() {
    let answer = Solution::create_binary_tree(vec![
        vec![39, 70, 1],
        vec![13, 39, 1],
        vec![85, 74, 1],
        vec![74, 13, 1],
        vec![38, 82, 1],
        vec![82, 85, 1],
    ]);
    println!("{answer:?}");
}
