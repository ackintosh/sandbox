// https://leetcode.com/problems/maximum-ice-cream-bars/

use std::collections::HashMap;

struct Solution;

impl Solution {
    // official
    // https://leetcode.com/problems/maximum-ice-cream-bars/solutions/2885725/maximum-ice-cream-bars/?orderBy=most_votes
    pub fn max_ice_cream(costs: Vec<i32>, mut coins: i32) -> i32 {
        // counting sort
        let mut answer = 0;

        let mut map = HashMap::new();
        let mut max_cost = 0;
        for c in costs {
            let v = map.entry(c).or_insert(0);
            *v += 1;

            if max_cost < c {
                max_cost = c;
            }
        }

        for cost in 1..=max_cost {
            if let Some(count) = map.get(&cost) {
                if coins >= (cost * count) {
                    coins -= cost * count;
                    answer += count;
                } else {
                    answer += coins / cost;
                    return answer;
                }
            }
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(4, Solution::max_ice_cream(vec![1, 3, 2, 4, 1], 7));
    assert_eq!(0, Solution::max_ice_cream(vec![10, 6, 8, 7, 7, 8], 5));
    assert_eq!(6, Solution::max_ice_cream(vec![1, 6, 3, 1, 2, 5], 20));
}
