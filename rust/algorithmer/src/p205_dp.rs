// キングとナイト

use std::convert::TryFrom;

struct Solution;

impl Solution {
    // ***パラメータ範囲***
    // size: 3 ~ 100
    // start, end: 1 ~ size-1
    // num_move: 1 ~ 50

    // start, end: 最初の要素は列位置、2番目の要素は行位置
    fn dp(size: usize, start: (usize, usize), end: (usize, usize), num_move: i32) -> i32 {
        // let mut table = [[[0; 100]; 100]; 50]; // ベクターではなく配列を使う場合は、パラメータ範囲の上限の大きさで作っておく
        let mut table = vec![vec![vec![0; size]; size]; usize::try_from(num_move).unwrap()];

        for step in 0..num_move {
            let step = usize::try_from(step).unwrap();
            if step == 0 {
                Self::count_moves(start.0, start.1, step, &mut table);
                continue;
            }

            for s in 0..size {
                for e in 0..size {
                    if table[step - 1][s][e] != 0 {
                        Self::count_moves(s, e, step, &mut table);
                    }
                }
            }
        }

        // println!("{:?}", table);
        let result_step = usize::try_from(num_move - 1).unwrap();
        // println!("{:?}", table[result_step]);

        table[result_step][end.0][end.1]
    }

    fn count_moves(x: usize, y: usize, step: usize, table: &mut Vec<Vec<Vec<i32>>>) {
        // キングナイトの移動範囲 (列位置, 行位置)
        //
        //           (-1, -2),          (1, -2),
        // (-2, -1), (-1, -1), (0, -1), (1, -1), (2, -1),
        //           (-1,  0),          (1,  0),
        // (-2,  1), (-1,  1), (0,  1), (1,  1), (2,  1),
        //           (-1,  2),          (1,  2),
        let moves = [
            (-1, -2),
            (1, -2),
            (-2, -1),
            (-1, -1),
            (0, -1),
            (1, -1),
            (2, -1),
            (-1, 0),
            (1, 0),
            (-2, 1),
            (-1, 1),
            (0, 1),
            (1, 1),
            (2, 1),
            (-1, 2),
            (1, 2),
        ];

        let size_of_the_field = i32::try_from(table[step].len()).unwrap();

        for m in moves.iter() {
            let xm = {
                let xm = i32::try_from(x).unwrap() + m.0;
                // チェス盤の範囲を外れる場合はスキップする
                if xm < 0 || xm >= size_of_the_field {
                    continue;
                }
                usize::try_from(xm).unwrap()
            };
            let ym = {
                let ym = i32::try_from(y).unwrap() + m.1;
                // チェス盤の範囲を外れる場合はスキップする
                if ym < 0 || ym >= size_of_the_field {
                    continue;
                }
                usize::try_from(ym).unwrap()
            };

            table[step][xm][ym] += 1;
        }
    }
}

mod test {
    use crate::p205_dp::Solution;

    #[test]
    fn example0() {
        assert_eq!(1, Solution::dp(3, (0, 0), (1, 0), 1));
    }

    #[test]
    fn example1() {
        assert_eq!(1, Solution::dp(3, (0, 0), (1, 2), 1));
    }

    #[test]
    fn example2() {
        assert_eq!(0, Solution::dp(3, (0, 0), (2, 2), 1));
    }

    #[test]
    fn example3() {
        assert_eq!(5, Solution::dp(3, (0, 0), (0, 0), 2));
    }
}
