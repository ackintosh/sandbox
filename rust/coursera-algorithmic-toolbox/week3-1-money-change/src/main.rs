// https://www.coursera.org/learn/algorithmic-toolbox/programming/kAiGl/programming-assignment-3-greedy-algorithms

use std::str::FromStr;

fn main() {
    let m = {
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();
        u16::from_str(&buff.trim()).unwrap()
    };
    println!("{}", money_change(m));
}

fn money_change(mut m: u16) -> u16 {
    let coins = vec![10, 5, 1];
    let mut number_of_coins = 0;

    for coin in coins {
        if m == 0 {
            break;
        }
        number_of_coins += m / coin;
        m = m % coin;
    }

    number_of_coins
}

#[test]
fn test_money_change() {
    assert_eq!(2, money_change(2));
    assert_eq!(6, money_change(28));
}
