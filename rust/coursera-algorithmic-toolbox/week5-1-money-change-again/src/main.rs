// https://www.coursera.org/learn/algorithmic-toolbox/programming/ekN4T/programming-assignment-5-dynamic-programming-1

use std::collections::HashMap;

const COINS: [u8; 3] = [1, 3, 4];

fn main() {
    let money = read_num();
    println!("{}", dp(money));
}

fn read_num() -> u32 {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    buff.trim().parse::<u32>().unwrap()
}

// input: money
// output: the minimum number of coins that changes money
fn dp(money: u32) -> u32 {
    let mut minimum_coins: HashMap<u32, u32> = HashMap::new();
    minimum_coins.insert(0, 0);

    for i in 1..=money {
        minimum_coins.insert(i, std::u32::MAX);
        for coin in COINS.iter() {
            match i.checked_sub(*coin as u32) {
                None => {}
                Some(remaining) => {
                    let number_of_coins = minimum_coins.get(&remaining).unwrap() + 1;
                    if &number_of_coins < minimum_coins.get(&i).unwrap() {
                        minimum_coins.insert(i, number_of_coins);
                    }
                }
            }
        }
    }

    *minimum_coins.get(&money).unwrap()
}

mod test {
    #[test]
    fn test_dp() {
        assert_eq!(2, crate::dp(2));
        assert_eq!(2, crate::dp(6));
        assert_eq!(9, crate::dp(34));
    }
}
