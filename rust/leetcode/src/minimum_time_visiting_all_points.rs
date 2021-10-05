// https://leetcode.com/problems/minimum-time-visiting-all-points/

struct Solution;

impl Solution {
    pub fn min_time_to_visit_all_points(points: Vec<Vec<i32>>) -> i32 {
        let mut result = 0;
        for i in 0..(points.len() - 1) {
            result += Self::calculate_time(&points[i], &points[i + 1]);
        }
        result
    }

    fn calculate_time(p1: &[i32], p2: &[i32]) -> i32 {
        let vertical_diff = (p1[0] - p2[0]).abs();
        let horizontal_diff = (p1[1] - p2[1]).abs();

        vertical_diff.max(horizontal_diff)
    }
}

#[test]
fn test() {
    assert_eq!(
        7,
        Solution::min_time_to_visit_all_points(vec![vec![1, 1], vec![3, 4], vec![-1, 0],])
    );
}
