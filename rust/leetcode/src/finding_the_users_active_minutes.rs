// https://leetcode.com/problems/finding-the-users-active-minutes/

struct Solution;

impl Solution {
    pub fn finding_users_active_minutes(logs: Vec<Vec<i32>>, k: i32) -> Vec<i32> {
        let mut counts = vec![0; k as usize];

        let mut user_ids = logs.iter().map(|log| log[0]).collect::<Vec<i32>>();
        user_ids.sort_unstable();
        user_ids.dedup();
        for u in user_ids {
            let mut times = logs
                .iter()
                .filter(|l| l[0] == u)
                .map(|l| l[1])
                .collect::<Vec<i32>>();
            times.sort_unstable();
            times.dedup();
            let v = counts.get_mut(times.len() - 1).expect("should have value");
            *v += 1;
        }

        counts
    }
}

mod test {
    use crate::finding_the_users_active_minutes::Solution;

    #[test]
    fn example1() {
        assert_eq!(
            vec![0, 2, 0, 0, 0],
            Solution::finding_users_active_minutes(
                vec![vec![0, 5], vec![1, 2], vec![0, 2], vec![0, 5], vec![1, 3]],
                5,
            )
        );
    }

    #[test]
    fn example2() {
        assert_eq!(
            vec![1, 1, 0, 0],
            Solution::finding_users_active_minutes(vec![vec![1, 1], vec![2, 2], vec![2, 3]], 4,)
        );
    }
}
