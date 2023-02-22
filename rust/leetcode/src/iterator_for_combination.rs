// https://leetcode.com/problems/iterator-for-combination/description/

use std::collections::VecDeque;

struct CombinationIterator {
    combinations: VecDeque<String>,
}

/**
 * `&self` means the method takes an immutable reference.
 * If you need a mutable reference, change it to `&mut self` instead.
 */
impl CombinationIterator {
    fn new(characters: String, combination_length: i32) -> Self {
        let mut combinations = VecDeque::new();

        for pos in 0..=(characters.len() - combination_length as usize) {
            dfs(
                characters.as_str(),
                pos,
                "".into(),
                combination_length as usize,
                &mut combinations,
            );
        }

        // println!("{:?}", combinations);

        CombinationIterator { combinations }
    }

    fn next(&mut self) -> String {
        self.combinations.pop_front().unwrap()
    }

    fn has_next(&self) -> bool {
        !self.combinations.is_empty()
    }
}

fn dfs(
    chars: &str,
    pos: usize,
    mut s: String,
    combination_length: usize,
    combinations: &mut VecDeque<String>,
) {
    // println!("pos: {pos}, s: {s}");
    s = format!("{s}{}", chars.get(pos..=pos).unwrap());

    if s.len() == combination_length {
        combinations.push_back(s);
        return;
    }

    let next_pos_max = chars.len() - (combination_length - s.len());
    // println!("next_pos_max: {next_pos_max}");
    for next_pos in (pos + 1)..=next_pos_max {
        dfs(chars, next_pos, s.clone(), combination_length, combinations);
    }
}

#[test]
fn test() {
    let mut ci = CombinationIterator::new("abc".into(), 2);
    assert_eq!("ab".to_string(), ci.next());
    assert!(ci.has_next());
    assert_eq!("ac".to_string(), ci.next());
    assert!(ci.has_next());
    assert_eq!("bc".to_string(), ci.next());
    assert!(!ci.has_next());
}
