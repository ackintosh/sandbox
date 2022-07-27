// https://leetcode.com/problems/watering-plants/

struct Solution;

impl Solution {
    pub fn watering_plants(plants: Vec<i32>, capacity: i32) -> i32 {
        let mut steps = 0;
        let mut can = capacity;

        for (i, w) in plants.iter().enumerate() {
            if &can >= w {
                // i番目に進んで、水をあげる
                steps += 1;
                can -= *w;
            } else {
                // 水場に戻って、水を汲む
                steps += (
                    i as i32
                    // 現在地(i - 1 番目) から水場 (-1番目) に戻る step 数
                ) * 2; // 行きと帰りで * 2
                can = capacity;

                // i番目に進んで、水をあげる
                steps += 1;
                can -= *w;
            }
        }

        steps
    }
}

#[test]
fn test() {
    assert_eq!(14, Solution::watering_plants(vec![2, 2, 3, 3], 5));
}
