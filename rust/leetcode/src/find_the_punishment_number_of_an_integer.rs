struct Solution;

impl Solution {
    pub fn punishment_number(n: i32) -> i32 {
        let mut answer = 0;

        for i in 1..=n {
            // println!("*** {i} ***");
            let square = i * i;
            let square_string = square.to_string();
            // println!("  --> square:{square_string}, len:{}", square_string.len());

            for split_at in 1..=square_string.len() {
                // println!("  ----> split_at:{split_at}");
                let (s1, s2) = square_string.split_at(split_at);
                // println!("  ----> split:{s1}, {s2}");
                if Self::is_the_number(i, vec![s1.parse::<i32>().unwrap()], String::from(s2)) {
                    // println!("  ------> the number: {i} {square}");
                    answer += square;
                    break;
                }
            }
        }

        answer
    }

    fn is_the_number(i: i32, list: Vec<i32>, remaining_string: String) -> bool {
        let summed: i32 = list.iter().sum();

        if remaining_string.len() == 0 {
            summed == i
        } else {
            let parsed = remaining_string.parse::<i32>().unwrap();
            if summed + parsed == i {
                true
            } else {
                for split_at in 1..=remaining_string.len() {
                    let (s1, s2) = remaining_string.split_at(split_at);
                    // println!("  [is_the_number] ----> split: {list:?} {s1}, {s2}");
                    let mut l = list.clone();
                    l.push(s1.parse::<i32>().unwrap());
                    if Self::is_the_number(i, l, String::from(s2)) {
                        return true;
                    }
                }
                false
            }
        }
    }
}

#[test]
fn example1() {
    assert_eq!(182, Solution::punishment_number(10));
    assert_eq!(1478, Solution::punishment_number(37));
    assert_eq!(21533, Solution::punishment_number(91));
}
