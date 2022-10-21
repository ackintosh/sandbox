// https://leetcode.com/problems/subdomain-visit-count/

use std::collections::hash_map::Entry;
use std::collections::HashMap;

struct Solution;

impl Solution {
    pub fn subdomain_visits(cpdomains: Vec<String>) -> Vec<String> {
        let mut visits: HashMap<String, u32> = HashMap::new();

        for cpdomain in cpdomains {
            let (count, domain) = {
                let s = cpdomain.split(" ").collect::<Vec<_>>();
                (s[0].parse::<u32>().unwrap(), String::from(s[1]))
            };

            let mut dstrings = vec![];
            for &d in domain.split(".").collect::<Vec<_>>().iter().rev() {
                dstrings.insert(0, d.to_string());
                match visits.entry(dstrings.join(".")) {
                    Entry::Occupied(mut entry) => {
                        let v = entry.get_mut();
                        *v += count;
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(count);
                    }
                }
            }
        }

        // println!("{:?}", visits);

        visits
            .iter()
            .map(|(domain, count)| format!("{} {}", count, domain))
            .collect::<Vec<_>>()
    }
}

#[test]
fn test() {
    let answer = Solution::subdomain_visits(vec!["9001 discuss.leetcode.com".into()]);
    assert_eq!(3, answer.len());

    let expected = vec![
        "9001 leetcode.com".to_string(),
        "9001 discuss.leetcode.com".to_string(),
        "9001 com".to_string(),
    ];

    for a in answer {
        assert!(expected.contains(&a));
    }
}
