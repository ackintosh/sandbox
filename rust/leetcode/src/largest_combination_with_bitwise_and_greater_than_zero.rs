// https://leetcode.com/problems/largest-combination-with-bitwise-and-greater-than-zero/

struct Solution;

impl Solution {
    pub fn largest_combination(candidates: Vec<i32>) -> i32 {
        // let mut answer = 0;
        // Self::dfs(i32::MAX, candidates, 0, &mut answer);
        // answer

        Self::count_bits(candidates)
    }

    // https://leetcode.com/problems/largest-combination-with-bitwise-and-greater-than-zero/solutions/2039903/java-c-python-bit-solution/
    fn count_bits(candidates: Vec<i32>) -> i32 {
        let mut answer = 0;

        for bit_pos in 0..24 {
            let mut count = 0;
            for c in candidates.iter() {
                count += (c >> bit_pos) & 1;
            }

            answer = answer.max(count);
        }

        answer
    }

    // fn dfs(bitwise: i32, candidates: Vec<i32>, mut size: i32, answer: &mut i32) {
    //     if candidates.is_empty() {
    //         return;
    //     }
    //
    //     size += 1;
    //
    //     for (index, num) in candidates.iter().enumerate() {
    //         let b = bitwise & *num;
    //         if b > 0 {
    //             if size > *answer {
    //                 *answer = size;
    //             }
    //
    //             let mut new_candidates = candidates.clone();
    //             let _ = new_candidates.remove(index);
    //             Self::dfs(b, new_candidates, size, answer);
    //         }
    //     }
    // }
}

#[test]
fn test() {
    assert_eq!(
        4,
        Solution::largest_combination(vec![16, 17, 71, 62, 12, 24, 14])
    );
    assert_eq!(2, Solution::largest_combination(vec![8, 8]));

    println!(
        "{}",
        Solution::largest_combination(vec![
            10, 72, 58, 33, 36, 70, 12, 88, 9, 48, 78, 97, 87, 19, 78, 9, 47, 73
        ])
    );
}
