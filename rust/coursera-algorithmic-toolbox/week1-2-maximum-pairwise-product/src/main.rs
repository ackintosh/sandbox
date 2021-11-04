use std::convert::TryFrom;
use std::str::FromStr;

fn main() {
    let n = {
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();
        u64::from_str(&buff.trim()).unwrap()
    };

    let nums = {
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();
        let words = buff.split_whitespace();
        words.map(|w| u64::from_str(w).unwrap()).collect::<Vec<_>>()
    };

    println!("{}", naive_algorithm(n, nums));
}

fn naive_algorithm(n: u64, nums: Vec<u64>) -> u64 {
    let mut result = 0;
    for i in 0..n {
        for j in (i + 1)..n {
            result = result.max(
                nums[usize::try_from(i).unwrap()]
                    .checked_mul(nums[usize::try_from(j).unwrap()])
                    .unwrap(),
            );
        }
    }

    result
}

#[test]
fn test_naive_algorithm() {
    // sample1
    assert_eq!(6, naive_algorithm(3, vec![1, 2, 3]));
    // sample2
    assert_eq!(
        140,
        naive_algorithm(10, vec![7, 5, 14, 2, 8, 8, 10, 1, 2, 3])
    );

    assert_eq!(9000000000, naive_algorithm(2, vec![100000, 90000]));
}
