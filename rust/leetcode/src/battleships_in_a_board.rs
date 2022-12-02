// https://leetcode.com/problems/battleships-in-a-board/

struct Solution;

impl Solution {
    pub fn count_battleships(board: Vec<Vec<char>>) -> i32 {
        let mut answer = 0;

        let num_column = board[0].len();
        let num_row = board.len();

        for r in 0..num_row {
            for c in 0..num_column {
                if board[r][c] == '.' {
                    continue;
                }

                if !Self::is_in_battleship(&board, r, c) {
                    answer += 1;
                }
            }
        }

        answer
    }

    // This function assumes the current position is X.
    fn is_in_battleship(board: &Vec<Vec<char>>, r: usize, c: usize) -> bool {
        if r == 0 && c == 0 {
            return false;
        }

        if r > 0 && board[r - 1][c] == 'X' {
            return true;
        }

        if c > 0 && board[r][c - 1] == 'X' {
            return true;
        }

        return false;
    }
}

#[test]
fn test() {
    assert_eq!(
        2,
        Solution::count_battleships(vec![
            vec!['X', '.', '.', 'X'],
            vec!['.', '.', '.', 'X'],
            vec!['.', '.', '.', 'X']
        ])
    );
}
