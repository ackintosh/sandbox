// https://leetcode.com/problems/all-paths-from-source-to-target/

use std::cell::RefCell;
use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn all_paths_source_target(graph: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        let goal = i32::try_from(graph.len() - 1).unwrap();
        let graph_refcell = RefCell::new(graph);
        let path = vec![];

        Self::solution(graph_refcell, path, 0, &goal)
    }

    fn solution(
        graph: RefCell<Vec<Vec<i32>>>,
        mut path: Vec<i32>,
        node: i32,
        goal: &i32,
    ) -> Vec<Vec<i32>> {
        path.push(node);

        let graph_borrowed = graph.borrow();
        let next_nodes = graph_borrowed.get(usize::try_from(node).unwrap()).unwrap();

        if node == *goal {
            return vec![path];
        }

        if next_nodes.is_empty() {
            return vec![];
        }

        let mut result = vec![];
        next_nodes.iter().for_each(|next_node| {
            Self::solution(graph.clone(), path.clone(), *next_node, goal)
                .iter()
                .for_each(|p| {
                    result.push(p.clone());
                })
        });

        result
    }
}

#[test]
fn example1() {
    let result = Solution::all_paths_source_target(vec![vec![1, 2], vec![3], vec![3], vec![]]);
    println!("{:?}", result);
}

#[test]
fn example_x() {
    // Input
    // [[4,3,1],[3,2,4],[],[4],[]]
    // Expected
    // [[0,4],[0,3,4],[0,1,3,4],[0,1,4]]
    let result = Solution::all_paths_source_target(vec![
        vec![4, 3, 1],
        vec![3, 2, 4],
        vec![],
        vec![4],
        vec![],
    ]);
    println!("{:?}", result);
}

#[test]
fn example_xx() {
    // Input
    // [[2],[],[1]]
    // Expected
    // [[0,2]]
    let result = Solution::all_paths_source_target(vec![vec![2], vec![], vec![1]]);
    println!("{:?}", result);
}
