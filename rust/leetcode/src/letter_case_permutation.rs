// https://leetcode.com/problems/letter-case-permutation/

use std::str::Chars;

struct Solution;

impl Solution {
    // ref https://leetcode.com/problems/letter-case-permutation/solutions/115485/java-easy-bfs-dfs-solution-with-explanation/?orderBy=most_votes
    pub fn letter_case_permutation(s: String) -> Vec<String> {
        let mut answer = vec![];

        Self::dfs(s.chars(), "".into(), &mut answer);

        answer
    }

    fn dfs(mut chars: Chars, mut str: String, answer: &mut Vec<String>) {
        if let Some(c) = chars.next() {
            if c.is_digit(10) {
                str.push(c);
                Self::dfs(chars, str, answer);
            } else {
                let mut str1 = str.clone();
                str1.push_str(c.to_lowercase().to_string().as_str());
                Self::dfs(chars.clone(), str1, answer);

                str.push_str(c.to_uppercase().to_string().as_str());
                Self::dfs(chars.clone(), str, answer);
            }
        } else {
            answer.push(str);
        }
    }
}

#[test]
fn test() {
    let answer = Solution::letter_case_permutation("a1b2".into());
    println!("{:?}", answer);
    let answer = Solution::letter_case_permutation("3z4".into());
    println!("{:?}", answer);
}
