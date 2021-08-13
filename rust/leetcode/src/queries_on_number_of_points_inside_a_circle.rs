// https://leetcode.com/problems/queries-on-number-of-points-inside-a-circle/

struct Solution;

impl Solution {
    pub fn count_points(points: Vec<Vec<i32>>, queries: Vec<Vec<i32>>) -> Vec<i32> {
        queries
            .iter()
            .map(|query| {
                points
                    .iter()
                    .map(|point| if Self::is_inside(point, query) { 1 } else { 0 })
                    .sum()
            })
            .collect()
    }

    fn is_inside(point: &[i32], query: &[i32]) -> bool {
        println!("=== is_inside() ===");
        println!("point: x={}, y={}", point[0], point[1]);
        println!("query: x={}, y={}", query[0], query[1]);
        let x = (point[0] - query[0]).pow(2);
        let y = (point[1] - query[1]).pow(2);

        let distance = ((x + y) as f32).sqrt();
        println!("distance: {}", distance);
        println!("radius: {}", query[2] as f32);

        let result = distance <= query[2] as f32;
        println!("result: {}", result);
        println!();
        result
    }
}

mod test {
    use crate::queries_on_number_of_points_inside_a_circle::Solution;

    #[test]
    fn example1() {
        assert_eq!(
            vec![3, 2, 2],
            Solution::count_points(
                vec![vec![1, 3], vec![3, 3], vec![5, 3], vec![2, 2]],
                vec![vec![2, 3, 1], vec![4, 3, 1], vec![1, 1, 2]]
            )
        );
    }

    #[test]
    fn example2() {
        assert_eq!(
            vec![2, 3, 2, 4],
            Solution::count_points(
                vec![vec![1, 1], vec![2, 2], vec![3, 3], vec![4, 4], vec![5, 5]],
                vec![vec![1, 2, 2], vec![2, 2, 2], vec![4, 3, 2], vec![4, 3, 3]],
            )
        );
    }

    #[test]
    fn example3() {
        assert_eq!(
            vec![11, 7, 8, 2, 7, 11, 13, 10, 10, 14, 3, 3],
            Solution::count_points(
                vec![
                    vec![99, 113],
                    vec![150, 165],
                    vec![23, 65],
                    vec![175, 154],
                    vec![84, 83],
                    vec![24, 59],
                    vec![124, 29],
                    vec![19, 97],
                    vec![117, 182],
                    vec![105, 191],
                    vec![83, 117],
                    vec![114, 35],
                    vec![0, 111],
                    vec![22, 53]
                ],
                vec![
                    vec![105, 191, 155],
                    vec![114, 35, 94],
                    vec![84, 83, 68],
                    vec![175, 154, 28],
                    vec![99, 113, 80],
                    vec![175, 154, 177],
                    vec![175, 154, 181],
                    vec![114, 35, 134],
                    vec![22, 53, 105],
                    vec![124, 29, 164],
                    vec![6, 99, 39],
                    vec![84, 83, 35]
                ]
            )
        );
    }
}
