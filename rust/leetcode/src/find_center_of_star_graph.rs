// https://leetcode.com/problems/find-center-of-star-graph/

struct Solution;

impl Solution {
    pub fn find_center(edges: Vec<Vec<i32>>) -> i32 {
        let first = &edges[0];
        let second = &edges[1];

        if first[0] == second[0] || first[0] == second[1] {
            first[0]
        } else if first[1] == second[0] || first[1] == second[1] {
            first[1]
        } else {
            panic!();
        }
    }
}

mod test {
    use crate::find_center_of_star_graph::Solution;

    #[test]
    fn example1() {
        assert_eq!(
            2,
            Solution::find_center(vec![vec![1, 2], vec![2, 3], vec![4, 2]])
        );
    }

    #[test]
    fn example2() {
        assert_eq!(
            1,
            Solution::find_center(vec![vec![1, 2], vec![5, 1], vec![1, 3], vec![1, 4]])
        );
    }
}
