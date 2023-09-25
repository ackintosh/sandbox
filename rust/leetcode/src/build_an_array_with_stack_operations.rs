// https://leetcode.com/problems/build-an-array-with-stack-operations/

struct Solution;

impl Solution {
    pub fn build_array(target: Vec<i32>, n: i32) -> Vec<String> {
        let mut answer = vec![];

        let mut prev_t = 0;

        for t in target {
            let diff = t - prev_t;

            for _ in 0..(diff - 1) {
                answer.push("Push".to_string());
                answer.push("Pop".to_string());
            }

            answer.push("Push".to_string());
            prev_t = t;
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![
            "Push".to_string(),
            "Push".to_string(),
            "Pop".to_string(),
            "Push".to_string()
        ],
        Solution::build_array(vec![1, 3], 3)
    );
    assert_eq!(
        vec!["Push".to_string(), "Push".to_string(), "Push".to_string()],
        Solution::build_array(vec![1, 2, 3], 3)
    );
    assert_eq!(
        vec!["Push".to_string(), "Push".to_string()],
        Solution::build_array(vec![1, 2], 4)
    );
}
