// https://leetcode.com/problems/generate-parentheses/

struct Solution;

impl Solution {
    pub fn generate_parenthesis(n: i32) -> Vec<String> {
        let mut answer = vec![];

        Self::dfs(n, n, String::new(), &mut answer);

        answer
    }

    fn dfs(o: i32, c: i32, str: String, answer: &mut Vec<String>) {
        if o == 0 && c == 0 {
            answer.push(str);
            return;
        }

        if o > 0 {
            let mut ostr = str.clone();
            ostr.push('(');
            Self::dfs(o - 1, c, ostr, answer);
        }
        if c > o {
            let mut cstr = str.clone();
            cstr.push(')');
            Self::dfs(o, c - 1, cstr, answer);
        }
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![
            "((()))".to_string(),
            "(()())".to_string(),
            "(())()".to_string(),
            "()(())".to_string(),
            "()()()".to_string()
        ],
        Solution::generate_parenthesis(3)
    );
    assert_eq!(vec!["()".to_string()], Solution::generate_parenthesis(1));
}
