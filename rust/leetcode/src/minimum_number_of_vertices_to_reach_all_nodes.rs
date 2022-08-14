// https://leetcode.com/problems/minimum-number-of-vertices-to-reach-all-nodes/

use std::collections::hash_map::Entry;
use std::collections::HashMap;

struct Solution;

impl Solution {
    pub fn find_smallest_set_of_vertices(_n: i32, edges: Vec<Vec<i32>>) -> Vec<i32> {
        let mut incoming_edges: HashMap<i32, Vec<i32>> = HashMap::new();
        for e in &edges {
            match incoming_edges.entry(e[1]) {
                Entry::Occupied(mut ent) => ent.get_mut().push(e[0]),
                Entry::Vacant(ent) => {
                    let _ = ent.insert(vec![e[0]]);
                }
            }
        }

        // println!("{:?}", incoming_edges);
        Self::find_origin_nodes(&edges, &incoming_edges)
    }

    // Find a node that does not have any incoming edge.
    fn find_origin_nodes(
        edges: &Vec<Vec<i32>>,
        incoming_edges: &HashMap<i32, Vec<i32>>,
    ) -> Vec<i32> {
        let mut result = vec![];

        for e in edges {
            if incoming_edges.get(&e[0]).is_none() && !result.contains(&e[0]) {
                result.push(e[0]);
            }
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![0, 3],
        Solution::find_smallest_set_of_vertices(
            6,
            vec![vec![0, 1], vec![0, 2], vec![2, 5], vec![3, 4], vec![4, 2]],
        )
    );
}
