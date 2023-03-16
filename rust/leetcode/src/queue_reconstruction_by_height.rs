// https://leetcode.com/problems/queue-reconstruction-by-height/

struct Solution;

impl Solution {
    // https://leetcode.com/problems/queue-reconstruction-by-height/solutions/89345/easy-concept-with-python-c-java-solution/?orderBy=most_votes
    pub fn reconstruct_queue(mut people: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        let mut answer = vec![];

        people.sort_by_key(|i| (-i[0], i[1]));

        while !people.is_empty() {
            let p = people.remove(0);
            let index = p[1] as usize;
            answer.insert(index, p);
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![
            vec![5, 0],
            vec![7, 0],
            vec![5, 2],
            vec![6, 1],
            vec![4, 4],
            vec![7, 1]
        ],
        Solution::reconstruct_queue(vec![
            vec![7, 0],
            vec![4, 4],
            vec![7, 1],
            vec![5, 0],
            vec![6, 1],
            vec![5, 2]
        ])
    );
}
