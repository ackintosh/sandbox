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

fn fast_algorithm(n: u64, nums: Vec<u64>) -> u64 {
    let largest_index = {
        let mut index = 0_usize;
        let mut number = 0;
        for i in 0..usize::try_from(n).unwrap() {
            if nums[i] > number {
                index = i;
                number = nums[i];
            }
        }

        index
    };

    let second_largest_index = {
        let mut index = 0_usize;
        let mut number = 0;
        for i in 1..usize::try_from(n).unwrap() {
            if i != largest_index && nums[i] > number {
                index = i;
                number = nums[i];
            }
        }

        index
    };

    nums[largest_index]
        .checked_mul(nums[second_largest_index])
        .unwrap()
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

#[test]
fn test_fast_algorithm() {
    // sample1
    assert_eq!(6, fast_algorithm(3, vec![1, 2, 3]));
    // sample2
    assert_eq!(
        140,
        fast_algorithm(10, vec![7, 5, 14, 2, 8, 8, 10, 1, 2, 3])
    );

    assert_eq!(9000000000, fast_algorithm(2, vec![100000, 90000]));
}

#[test]
fn test_fast_algorithm_on_large_data_sets() {
    let n: u64 = 2_u64 * 10_u64.checked_pow(5).unwrap();
    let mut nums = vec![];
    for i in 1..=n {
        nums.push(i);
    }

    assert_eq!(39999800000, fast_algorithm(n, nums));
}
