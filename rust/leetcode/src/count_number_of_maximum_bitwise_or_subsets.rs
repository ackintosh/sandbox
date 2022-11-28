// https://leetcode.com/problems/count-number-of-maximum-bitwise-or-subsets/

// ref: https://leetcode.com/problems/count-number-of-maximum-bitwise-or-subsets/discuss/1525309/JavaC%2B%2BPython-DP-solution

use std::collections::hash_map::Entry;
use std::collections::HashMap;

struct Solution;

impl Solution {
    pub fn count_max_or_subsets(nums: Vec<i32>) -> i32 {
        let mut counts: HashMap<i32, i32> = HashMap::new();
        counts.insert(0, 1);

        for n in nums {
            // println!("n: {n}");

            let key_values = counts
                .iter()
                .map(|(k, v)| (*k, *v))
                .collect::<Vec<(i32, i32)>>();
            // let key_values = counts.keys().map(|n| (*n, *counts.get(n).unwrap())).collect::<Vec<(i32, i32)>>();
            // println!("    key_values: {:?}", key_values);
            for (k, v) in key_values {
                let bitwise = n | k;
                // println!("    bitwise: {bitwise}");

                match counts.entry(bitwise) {
                    Entry::Occupied(mut entry) => {
                        let count = entry.get_mut();
                        // println!("    entry.get_mut: {count}");
                        *count += v;
                    }
                    Entry::Vacant(entry) => {
                        // println!("    vacant");
                        entry.insert(v);
                    }
                }
            }
            // println!("    counts: {counts:?}")
        }
        // println!("{:?}", counts);

        let k = counts.keys().max().unwrap();
        *counts.get(k).unwrap()
    }
}

#[test]
fn test() {
    assert_eq!(2, Solution::count_max_or_subsets(vec![3, 1]));
    assert_eq!(7, Solution::count_max_or_subsets(vec![2, 2, 2]));
    assert_eq!(6, Solution::count_max_or_subsets(vec![3, 2, 1, 5]));
}
