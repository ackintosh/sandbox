// https://leetcode.com/problems/unique-number-of-occurrences/

struct Solution;

impl Solution {
    pub fn unique_occurrences(mut arr: Vec<i32>) -> bool {
        let mut occurrences = vec![];
        let mut working = i32::max_value();
        let mut working_occurrence = 0;

        arr.sort_unstable();

        for n in arr.iter() {
            if working != *n {
                if occurrences.contains(&working_occurrence) {
                    return false;
                }
                occurrences.push(working_occurrence);
                working = *n;
                working_occurrence = 0;
            }
            working_occurrence += 1;
        }

        !occurrences.contains(&working_occurrence)
    }
}

#[test]
fn example1() {
    assert!(Solution::unique_occurrences(vec![1, 2, 2, 1, 1, 3]));
}

#[test]
fn example2() {
    assert!(!Solution::unique_occurrences(vec![1, 2]));
}

#[test]
fn example3() {
    assert!(Solution::unique_occurrences(vec![
        -3, 0, 1, -3, 1, 1, 1, -3, 10, 0
    ]));
}
