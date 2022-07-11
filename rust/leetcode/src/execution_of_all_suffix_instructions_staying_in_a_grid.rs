// https://leetcode.com/problems/execution-of-all-suffix-instructions-staying-in-a-grid/
struct Solution;

impl Solution {
    pub fn execute_instructions(n: i32, start_pos: Vec<i32>, s: String) -> Vec<i32> {
        let mut answer = vec![];

        for i in 0..s.len() {
            answer.push(Self::execute(n, &start_pos, &s[i..]));
        }

        answer
    }

    fn execute(n: i32, start_pos: &Vec<i32>, s: &str) -> i32 {
        let mut number_of_executed_instruction = 0;
        let mut row = start_pos[0];
        let mut col = start_pos[1];

        for c in s.chars() {
            match c {
                'R' => col += 1,
                'L' => col -= 1,
                'U' => row -= 1,
                'D' => row += 1,
                _ => unreachable!(),
            }

            if col < 0 || row < 0 || col >= n || row >= n {
                break;
            }

            number_of_executed_instruction += 1;
        }

        number_of_executed_instruction
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![1, 5, 4, 3, 1, 0],
        Solution::execute_instructions(3, vec![0, 1], "RRDDLU".to_owned())
    );
}
