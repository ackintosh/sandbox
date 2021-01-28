// https://leetcode.com/problems/max-increase-to-keep-city-skyline/

struct Solution;

impl Solution {
    #[allow(clippy::needless_range_loop)]
    pub fn max_increase_keeping_skyline(grid: Vec<Vec<i32>>) -> i32 {
        let skyline_top_or_bottom = {
            let mut result = vec![];
            let until = grid[0].len();
            for i in 0..until {
                let mut a = grid.iter().map(|g| *g.get(i).unwrap()).collect::<Vec<_>>();
                a.sort_unstable();
                result.push(*a.last().unwrap());
            }

            result
        };

        let skyline_left_or_right = grid
            .iter()
            .map(|g| {
                let mut t = g.clone();
                t.sort_unstable();
                *t.last().unwrap()
            })
            .collect::<Vec<_>>();

        // println!("skyline_top_or_bottom: {:?}", skyline_top_or_bottom);
        // println!("skyline_left_or_right: {:?}", skyline_left_or_right);

        let mut result = 0;
        for left_or_right in 0..grid.len() {
            for top_or_bottom in 0..grid[0].len() {
                let max =
                    skyline_left_or_right[left_or_right].min(skyline_top_or_bottom[top_or_bottom]);
                let v = grid[left_or_right][top_or_bottom];
                result += max.saturating_sub(v);
            }
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        Solution::max_increase_keeping_skyline(vec![
            vec![3, 0, 8, 4],
            vec![2, 4, 5, 7],
            vec![9, 2, 6, 3],
            vec![0, 3, 1, 0]
        ]),
        35
    );
}
