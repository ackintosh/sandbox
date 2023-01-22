// https://leetcode.com/problems/remove-all-occurrences-of-a-substring/

struct Solution;

impl Solution {
    // ref: https://leetcode.com/problems/remove-all-occurrences-of-a-substring/solutions/1298766/c-simple-solution-faster-than-100/?orderBy=most_votes
    pub fn remove_occurrences(s: String, part: String) -> String {
        let part_len = part.len();
        let mut answer = String::new();

        for c in s.chars() {
            answer.push(c);
            if answer.len() >= part.len() && &answer[(answer.len() - part_len)..] == &part {
                for _ in 0..part_len {
                    let _ = answer.pop();
                }
            }
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(
        "dab".to_string(),
        Solution::remove_occurrences("daabcbaabcbc".into(), "abc".into())
    );
    assert_eq!(
        "ab".to_string(),
        Solution::remove_occurrences("axxxxyyyyb".into(), "xy".into())
    );
}
