// https://leetcode.com/problems/the-k-th-lexicographical-string-of-all-happy-strings-of-length-n/

struct Solution;

impl Solution {
    pub fn get_happy_string(n: i32, k: i32) -> String {
        let mut found = 0;
        Self::dfs("".to_string(), n as usize, k, &mut found).unwrap_or("".into())
    }

    fn dfs(s: String, n: usize, k: i32, found: &mut i32) -> Option<String> {
        if s.len() == n {
            *found += 1;

            return if *found == k { Some(s) } else { None };
        }

        let last_char = s.chars().last().unwrap_or('x');
        let chars = vec!['a', 'b', 'c']
            .into_iter()
            .filter(|c| *c != last_char)
            .collect::<Vec<_>>();
        // println!("chars: {chars:?}");

        for c in chars {
            let mut ss = s.clone();
            ss.push(c);
            if let Some(answer) = Self::dfs(ss, n, k, found) {
                return Some(answer);
            }
        }

        return None;
    }
}

#[test]
fn test() {
    assert_eq!("c".to_string(), Solution::get_happy_string(1, 3));
    assert_eq!("".to_string(), Solution::get_happy_string(1, 4));
    assert_eq!("cab".to_string(), Solution::get_happy_string(3, 9));
}
