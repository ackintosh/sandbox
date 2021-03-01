// https://leetcode.com/problems/minimum-operations-to-make-array-equal/

struct Solution;

impl Solution {
    pub fn min_operations(n: i32) -> i32 {
        let middle_number = {
            let middle_index = n / 2;
            if n % 2 == 0 {
                middle_index * 2
            } else {
                middle_index * 2 + 1
            }
        };
        // println!("middle_number: {}", middle_number);

        let mut num_add_operation = 0;
        let mut num_sub_operation = 0;

        for nn in 0..n {
            let v = nn * 2 + 1;
            // println!("v: {}", v);
            match v.cmp(&middle_number) {
                std::cmp::Ordering::Greater => num_sub_operation += v - middle_number,
                std::cmp::Ordering::Less => num_add_operation += middle_number - v,
                std::cmp::Ordering::Equal => continue,
            }
        }

        // println!("num_add_operation: {}", num_add_operation);
        // println!("num_sub_operation: {}", num_sub_operation);
        num_add_operation.max(num_sub_operation)
    }
}

#[test]
fn example1() {
    assert_eq!(Solution::min_operations(3), 2);
}

#[test]
fn example2() {
    assert_eq!(Solution::min_operations(6), 9);
}
