// https://leetcode.com/problems/sort-the-students-by-their-kth-score/

struct Solution;

impl Solution {
    pub fn sort_the_students(score: Vec<Vec<i32>>, k: i32) -> Vec<Vec<i32>> {
        let mut score_to_index: Vec<(usize, i32)> = score
            .iter()
            .enumerate()
            .map(|(index, row)| (index, row[k as usize]))
            .collect::<Vec<_>>();

        score_to_index.sort_by(|a, b| {
            // Sort by the score from the highest to the lowest.
            b.1.cmp(&a.1)
        });

        score_to_index
            .iter()
            .map(|(index, _)| score[*index].clone())
            .collect::<Vec<_>>()
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![vec![7, 5, 11, 2], vec![10, 6, 9, 1], vec![4, 8, 3, 15]],
        Solution::sort_the_students(
            vec![vec![10, 6, 9, 1], vec![7, 5, 11, 2], vec![4, 8, 3, 15]],
            2
        )
    );

    assert_eq!(
        vec![vec![5, 6], vec![3, 4]],
        Solution::sort_the_students(vec![vec![3, 4], vec![5, 6]], 0)
    );
}
