// https://leetcode.com/problems/arithmetic-subarrays/

use std::convert::TryFrom;

struct Solution;

impl Solution {
    pub fn check_arithmetic_subarrays(nums: Vec<i32>, l: Vec<i32>, r: Vec<i32>) -> Vec<bool> {
        let mut result = vec![];
        for i in 0..l.len() {
            let l_index = usize::try_from(l[i]).unwrap();
            let r_index = usize::try_from(r[i]).unwrap();

            result.push(Self::is_arithmetic(&nums[l_index..=r_index]));
        }

        result
    }

    fn is_arithmetic(sub_slice: &[i32]) -> bool {
        let mut sub_array = Vec::from(sub_slice);
        sub_array.sort_unstable();

        let mut difference = None;

        for ii in 0..(sub_array.len() - 1) {
            let diff = sub_array[ii] - sub_array[ii + 1];

            if let Some(d) = difference {
                if diff != d {
                    return false;
                }
            } else {
                difference = Some(diff);
            }
        }

        true
    }
}

#[test]
fn example1() {
    assert_eq!(
        vec![true, false, true],
        Solution::check_arithmetic_subarrays(vec![4, 6, 5, 9, 3, 7], vec![0, 0, 2], vec![2, 3, 5])
    );
}
