// https://leetcode.com/problems/minimum-amount-of-time-to-collect-garbage/

struct Solution;

impl Solution {
    pub fn garbage_collection(garbage: Vec<String>, travel: Vec<i32>) -> i32 {
        let mut result = 0;

        for truck in ['M', 'G', 'P'] {
            result += Self::collect_garbage(truck, &garbage, &travel);
        }

        result
    }

    fn collect_garbage(truck: char, garbage: &Vec<String>, travel: &Vec<i32>) -> i32 {
        let max_garbage_index = {
            let mut index = None;
            for (i, g) in garbage.iter().enumerate() {
                if g.contains(truck) {
                    index = Some(i);
                }
            }

            if let Some(i) = index {
                i
            } else {
                return 0;
            }
        };

        let mut result = 0;
        let mut current_garbage_index = 0;
        while current_garbage_index <= max_garbage_index {
            // println!("{} {}", truck, current_garbage_index);
            if current_garbage_index > 0 {
                if let Some(t) = travel.get(current_garbage_index - 1) {
                    result += t;
                }
            }
            let g = garbage.get(current_garbage_index).unwrap();
            result += g.match_indices(truck).collect::<Vec<_>>().len() as i32;
            current_garbage_index += 1;
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        21,
        Solution::garbage_collection(
            vec!["G".into(), "P".into(), "GP".into(), "GG".into()],
            vec![2, 4, 3]
        )
    );

    assert_eq!(
        37,
        Solution::garbage_collection(
            vec!["MMM".into(), "PGM".into(), "GP".into()],
            vec![3, 10],
        )
    );
}
