struct Solution;

impl Solution {
    pub fn min_operations(nums: Vec<i32>, k: i32) -> i32 {
        let mut i = nums.iter();
        let first_elem = *i.next().unwrap();
        let nums_xor = i.fold(first_elem, |cur, next| cur ^ *next);
        // let s = format!("{:#034b}", nums_xor ^ k);
        // s.chars()
        //     .fold(0, |ret, c| if c == '1' { ret + 1 } else { ret })
        (nums_xor ^ k).count_ones() as i32
    }
}

#[test]
fn example1() {
    assert_eq!(2, Solution::min_operations(vec![2, 1, 3, 4], 1));
}

#[test]
fn example2() {
    assert_eq!(0, Solution::min_operations(vec![2, 0, 2, 0], 0));
}
