// https://leetcode.com/problems/find-all-duplicates-in-an-array/

struct Solution;

// ref: https://leetcode.com/problems/find-all-duplicates-in-an-array/discussion/comments/1568392

impl Solution {
    pub fn find_duplicates(mut nums: Vec<i32>) -> Vec<i32> {
        let mut answer = vec![];

        for i in 0..nums.len() {
            let value = nums.get(i).unwrap().clone().abs();
            let index_value = nums.get_mut(value as usize - 1).unwrap();

            if index_value.is_negative() {
                answer.push(value);
            } else {
                *index_value = -*index_value;
            }
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![2, 3],
        Solution::find_duplicates(vec![4, 3, 2, 7, 8, 2, 3, 1])
    );
    assert_eq!(vec![1], Solution::find_duplicates(vec![1, 1, 2]));
    assert_eq!(Vec::<i32>::new(), Solution::find_duplicates(vec![1]));
}
