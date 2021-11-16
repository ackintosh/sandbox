// https://www.coursera.org/learn/algorithmic-toolbox/programming/b66y2/programming-assignment-2-algorithmic-warm-up/submission

use std::str::FromStr;

fn main() {
    let (a, b) = {
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();
        let nums = &buff
            .trim()
            .split(' ')
            .collect::<Vec<&str>>()
            .iter()
            .map(|&s| u64::from_str(s).unwrap())
            .collect::<Vec<u64>>();
        (nums[0], nums[1])
    };

    let result = gcd(a.max(b), a.min(b));
    println!("{}", result);
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        return a;
    }

    let c = a % b;
    gcd(b, c)
}

#[test]
fn test_gcd() {
    assert_eq!(1, gcd(18, 35));
    assert_eq!(17657, gcd(28851538, 1183019));
}
