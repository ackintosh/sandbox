// https://leetcode.com/problems/lexicographically-smallest-equivalent-string/

use std::collections::HashMap;

struct Solution;

struct UnionFind {
    map: HashMap<char, char>,
}

impl UnionFind {
    fn new() -> Self {
        UnionFind {
            map: HashMap::new(),
        }
    }

    fn find(&mut self, x: char) -> char {
        if !self.map.contains_key(&x) {
            self.map.insert(x.clone(), x.clone());
        }

        let val = self.map.get(&x).unwrap().clone();
        if val == x {
            x
        } else {
            let root_val = self.find(val.clone());
            self.map.insert(val, root_val.clone());
            root_val
        }
    }

    fn union(&mut self, x: char, y: char) {
        let root_x = self.find(x);
        let root_y = self.find(y);

        if root_x < root_y {
            *self.map.get_mut(&root_y).unwrap() = root_x;
        } else {
            *self.map.get_mut(&root_x).unwrap() = root_y;
        }
    }
}

impl Solution {
    // https://leetcode.com/problems/lexicographically-smallest-equivalent-string/solutions/3047517/python3-union-find-template-explanations/
    pub fn smallest_equivalent_string(s1: String, s2: String, base_str: String) -> String {
        let mut uf = UnionFind::new();

        let mut s1chars = s1.chars();
        let mut s2chars = s2.chars();
        for _ in 0..s1.len() {
            let s1c = s1chars.next().unwrap();
            let s2c = s2chars.next().unwrap();
            uf.union(s1c, s2c);
        }

        let mut answer = String::new();
        for c in base_str.chars() {
            answer.push(uf.find(c));
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(
        "makkek".to_string(),
        Solution::smallest_equivalent_string(
            "parker".to_string(),
            "morris".to_string(),
            "parser".to_string()
        )
    );

    assert_eq!(
        "hdld".to_string(),
        Solution::smallest_equivalent_string(
            "hello".to_string(),
            "world".to_string(),
            "hold".to_string()
        )
    );

    assert_eq!(
        "aauaaaaada".to_string(),
        Solution::smallest_equivalent_string(
            "leetcode".to_string(),
            "programs".to_string(),
            "sourcecode".to_string()
        )
    );
}
