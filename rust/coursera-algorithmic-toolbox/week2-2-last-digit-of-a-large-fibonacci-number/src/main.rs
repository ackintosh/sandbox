// https://www.coursera.org/learn/algorithmic-toolbox/programming/b66y2/programming-assignment-2-algorithmic-warm-up/submission

use std::collections::HashMap;
use std::convert::TryFrom;
use std::str::FromStr;

fn main() {
    let n = {
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();
        u64::from_str(&buff.trim()).unwrap()
    };

    let result = last_digit_of_a_fibonacci_number(n);
    println!("{}", result);
}

fn last_digit_of_a_fibonacci_number(n: u64) -> i8 {
    let mut map: HashMap<usize, i8> = HashMap::new();
    map.insert(0, 0);
    map.insert(1, 1);
    let n_usize = usize::try_from(n).unwrap();
    for i in 2..=n_usize {
        map.insert(
            i,
            (map.get(&(i - 1)).unwrap() + map.get(&(i - 2)).unwrap()) % 10,
        );
    }
    map.get(&n_usize).unwrap().clone()
}

#[test]
fn test_last_digit_of_a_fibonacci_number() {
    assert_eq!(2, last_digit_of_a_fibonacci_number(3));
    assert_eq!(9, last_digit_of_a_fibonacci_number(331));
    assert_eq!(5, last_digit_of_a_fibonacci_number(327305));
}
