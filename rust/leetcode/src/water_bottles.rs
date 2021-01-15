// https://leetcode.com/problems/water-bottles/

struct Solution;

impl Solution {
    pub fn num_water_bottles(num_bottles: i32, num_exchange: i32) -> i32 {
        assert!(num_exchange > 1);

        // 飲んだボトルの数
        let mut count = 0;

        // 最初に渡される、満タンのボトルをすべて飲む
        count += num_bottles;
        let mut empty_bottles = num_bottles;

        loop {
            let exchanged = empty_bottles / num_exchange;
            if exchanged == 0 {
                break;
            }

            // 交換しきれなかった余りの空ボトル
            empty_bottles %= num_exchange;
            // 交換したボトルを飲む
            count += exchanged;
            // 交換したボトルを飲んだので、空ボトルに追加する
            empty_bottles += exchanged;
        }

        count
    }
}

#[test]
fn test() {
    assert_eq!(13, Solution::num_water_bottles(9, 3));
    assert_eq!(19, Solution::num_water_bottles(15, 4));
}
