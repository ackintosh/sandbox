// https://leetcode.com/problems/group-the-people-given-the-group-size-they-belong-to/

use std::collections::HashMap;
use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn group_the_people(group_sizes: Vec<i32>) -> Vec<Vec<i32>> {
        let mut people: HashMap<i32, Vec<i32>> = HashMap::new();

        for (person_id, group_size) in group_sizes.iter().enumerate() {
            match people.get_mut(group_size) {
                Some(group) => {
                    group.push(i32::try_from(person_id).unwrap());
                }
                _ => {
                    let group = vec![i32::try_from(person_id).unwrap()];
                    people.insert(*group_size, group);
                }
            };
        }

        let mut result = vec![];

        for (group_size, person_ids) in people {
            let mut working_vector = vec![];
            for id in person_ids {
                working_vector.push(id);
                if working_vector.len() == usize::try_from(group_size).unwrap() {
                    result.push(working_vector.clone());
                    working_vector.clear();
                }
            }
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        Solution::group_the_people(vec![3, 3, 3, 3, 3, 1, 3]),
        vec![vec![0, 1, 2], vec![3, 4, 6], vec![5]]
    )
}
