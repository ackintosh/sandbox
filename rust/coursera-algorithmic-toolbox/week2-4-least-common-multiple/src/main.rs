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

    let result = lcm(a.max(b), a.min(b));
    println!("{}", result);
}

fn lcm(a: u64, b: u64) -> u64 {
    // 公式としては a * b / d だが、
    // a * b でオーバーフローしてしまうのを避けるために
    // a / d * b に変形する
    let d = gcd(a, b);
    a.checked_div(d).unwrap().checked_mul(b).unwrap()
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        return a;
    }

    let c = a % b;
    gcd(b, c)
}

#[test]
fn test_lcm() {
    assert_eq!(24, lcm(6, 8));
    assert_eq!(1933053046, lcm(28851538, 1183019));
}
