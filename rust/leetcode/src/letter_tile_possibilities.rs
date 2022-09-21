// https://leetcode.com/problems/letter-tile-possibilities/

use std::collections::HashSet;
use std::ops::Index;

struct Solution;

impl Solution {
    pub fn num_tile_possibilities(tiles: String) -> i32 {
        let chars = tiles.chars().collect::<Vec<_>>();
        let mut paths = HashSet::new();

        Self::dfs("".into(), &chars, &mut paths);

        paths.len() as i32
    }

    fn dfs(path: String, tiles: &Vec<char>, paths: &mut HashSet<String>) {
        if !path.is_empty() {
            paths.insert(path.clone());
        }

        for i in 0..tiles.len() {
            let mut p = path.clone();
            p.push(tiles.index(i).clone());
            // println!("p: {}", p);
            let mut t = tiles[..i].to_vec();
            let t2 = tiles[i + 1..].to_vec();
            t.extend(t2);
            // println!("t: {:?}", t);
            Self::dfs(p, &t, paths);
        }
    }
}

#[test]
fn test() {
    assert_eq!(8, Solution::num_tile_possibilities("AAB".into()));
    assert_eq!(188, Solution::num_tile_possibilities("AAABBC".into()));
    assert_eq!(1, Solution::num_tile_possibilities("V".into()));
}
