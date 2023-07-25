// https://leetcode.com/problems/find-the-original-array-of-prefix-xor/description/

struct Solution;

impl Solution {
    pub fn find_array(pref: Vec<i32>) -> Vec<i32> {
        let mut answer = vec![];

        for i in 0..pref.len() {
            if i == 0 {
                answer.push(pref[i]);
            } else {
                answer.push(pref[i] ^ pref[i - 1]);
            }
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![5, 7, 2, 3, 2],
        Solution::find_array(vec![5, 2, 0, 3, 1])
    );
    assert_eq!(vec![13], Solution::find_array(vec![13]));
}
