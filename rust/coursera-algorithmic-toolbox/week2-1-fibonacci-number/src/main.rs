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

    // let result = naive_algorithm(n);
    let result = fast_algorithm(n);
    println!("{}", result);
}

fn naive_algorithm(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        n => naive_algorithm(n - 1) + naive_algorithm(n - 2),
    }
}

fn fast_algorithm(n: u64) -> u64 {
    let mut map: HashMap<usize, u64> = HashMap::new();
    let n_usize = usize::try_from(n).unwrap();
    map.insert(0, 0);
    map.insert(1, 1);
    for i in 2..=n_usize {
        map.insert(i, map.get(&(i - 1)).unwrap() + map.get(&(i - 2)).unwrap());
    }
    map.get(&n_usize).unwrap().clone()
}

#[test]
fn test_naive_algorithm() {
    assert_eq!(55, naive_algorithm(10));
}

#[test]
fn test_fast_algorithm() {
    assert_eq!(55, fast_algorithm(10));
}
