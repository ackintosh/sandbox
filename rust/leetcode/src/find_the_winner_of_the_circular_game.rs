// https://leetcode.com/problems/find-the-winner-of-the-circular-game/

struct Solution;

impl Solution {
    pub fn find_the_winner(n: i32, k: i32) -> i32 {
        let mut circle = (1..=n).collect::<Vec<i32>>();

        while circle.len() != 1 {
            let key_to_remove = (k - 1) as usize % circle.len();
            circle = Self::count_and_remove(circle, key_to_remove);
        }

        circle.pop().unwrap()
    }

    fn count_and_remove(mut circle: Vec<i32>, key_to_remove: usize) -> Vec<i32> {
        // println!("{:?}", circle);
        let _dropped = circle.remove(key_to_remove);
        // println!("dropped: {:?}", dropped);

        let mut new_circle = vec![];

        while let Some(_) = circle.get(key_to_remove) {
            new_circle.push(circle.remove(key_to_remove));
        }

        while !circle.is_empty() {
            new_circle.push(circle.remove(0));
        }

        // println!("{:?}", circle);
        // println!("{:?}", new_circle);
        new_circle
    }
}

#[test]
fn test() {
    assert_eq!(3, Solution::find_the_winner(5, 2));
    assert_eq!(1, Solution::find_the_winner(6, 5));
}
