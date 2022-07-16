// https://leetcode.com/problems/number-of-laser-beams-in-a-bank/

struct Solution;

impl Solution {
    pub fn number_of_beams(bank: Vec<String>) -> i32 {
        let mut result = 0;
        let mut current_devices = 0;

        for b in bank {
            let num_device = b.chars().filter(|&c| c == '1').count();
            if num_device == 0 {
                continue;
            }

            result += current_devices * num_device as i32;
            current_devices = num_device as i32;
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        8,
        Solution::number_of_beams(vec![
            "011001".to_string(),
            "000000".to_string(),
            "010100".to_string(),
            "001000".to_string()
        ])
    );
}
