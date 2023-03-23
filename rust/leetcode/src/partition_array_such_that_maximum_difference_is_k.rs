// https://leetcode.com/problems/partition-array-such-that-maximum-difference-is-k/description/

struct Solution;

impl Solution {
    // https://leetcode.com/problems/partition-array-such-that-maximum-difference-is-k/solutions/2112243/java-c-python-sort-greedy/?orderBy=most_votes
    pub fn partition_array(mut nums: Vec<i32>, k: i32) -> i32 {
        nums.sort_unstable();
        let mut answer = 1;

        let mut min = nums.first().unwrap();
        let mut max = nums.first().unwrap();
        for n in nums.iter() {
            min = min.min(n);
            max = max.max(n);
            if max - min > k {
                answer += 1;
                min = n;
                max = n;
            }
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(2, Solution::partition_array(vec![3, 6, 1, 2, 5], 2));
    assert_eq!(2, Solution::partition_array(vec![1, 2, 3], 1));
    assert_eq!(3, Solution::partition_array(vec![2, 2, 4, 5], 0));
}
