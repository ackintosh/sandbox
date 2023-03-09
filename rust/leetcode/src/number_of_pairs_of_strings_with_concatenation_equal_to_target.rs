// https://leetcode.com/problems/number-of-pairs-of-strings-with-concatenation-equal-to-target/

struct Solution;

impl Solution {
    pub fn num_of_pairs(nums: Vec<String>, target: String) -> i32 {
        let mut answer = 0;

        for i in 0..nums.len() {
            let mut other_nums = nums.clone();
            let s = other_nums.remove(i);
            Self::dfs(1, &mut answer, other_nums, s, &target);
        }

        answer
    }

    fn dfs(height: i32, answer: &mut i32, nums: Vec<String>, s: String, target: &str) {
        if height == 2 {
            if s.as_str() == target {
                *answer += 1;
            }
            return;
        }

        if !target.starts_with(&s) {
            return;
        }

        for i in 0..nums.len() {
            let mut other_nums = nums.clone();
            let ss = format!("{}{}", s, other_nums.remove(i));
            Self::dfs(height + 1, answer, other_nums, ss, target);
        }
    }
}

#[test]
fn test() {
    assert_eq!(
        4,
        Solution::num_of_pairs(
            vec!["777".into(), "7".into(), "77".into(), "77".into()],
            "7777".into()
        )
    );
    assert_eq!(
        2,
        Solution::num_of_pairs(
            vec!["123".into(), "4".into(), "12".into(), "34".into()],
            "1234".into()
        )
    );
    assert_eq!(
        6,
        Solution::num_of_pairs(vec!["1".into(), "1".into(), "1".into()], "11".into())
    );
    assert_eq!(
        0,
        Solution::num_of_pairs(vec!["7".into(), "7777".into()], "7777".into())
    );
    assert_eq!(
        13,
        Solution::num_of_pairs(
            vec![
                "7672198".into(),
                "767".into(),
                "221".into(),
                "698566842".into(),
                "2198903679".into(),
                "7672198".into(),
                "2198903679".into(),
                "76721989036".into(),
                "973".into(),
                "767219890367".into(),
                "2051569".into(),
                "903679".into(),
                "605513".into(),
                "7672".into(),
                "9".into(),
                "5".into(),
                "79".into(),
                "50".into(),
                "5657214709160".into(),
                "673123241121".into(),
                "3679".into(),
                "672198903679".into(),
                "903679".into(),
                "3651502".into(),
                "56".into(),
                "27".into(),
                "767219890".into(),
                "198903679".into(),
                "7".into(),
                "767".into()
            ],
            "7672198903679".into()
        )
    );
}
