// https://www.coursera.org/learn/algorithmic-toolbox/programming/kAiGl/programming-assignment-3-greedy-algorithms

use std::str::FromStr;

#[derive(Debug)]
struct Item {
    value: u32,
    weight: u32,
}

impl Item {
    fn new(value: u32, weight: u32) -> Self {
        Self { value, weight }
    }

    fn value_per_unit(&self) -> f64 {
        self.value as f64 / self.weight as f64
    }
}

fn main() {
    let (n, w) = {
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();
        let mut strs = buff.split_whitespace();

        let n = u16::from_str(strs.next().unwrap()).unwrap();
        let w = u32::from_str(strs.next().unwrap()).unwrap();
        (n, w)
    };

    let items = {
        let mut items = vec![];
        for _ in 0..n {
            let mut buff = String::new();
            std::io::stdin().read_line(&mut buff).unwrap();
            let mut strs = buff.split_whitespace();
            let value = u32::from_str(strs.next().unwrap()).unwrap();
            let weight = u32::from_str(strs.next().unwrap()).unwrap();
            items.push(Item::new(value, weight));
        }
        items
    };

    println!("{}", format(maximum_of_the_loot(w, items)));
}

fn maximum_of_the_loot(mut w: u32, mut items: Vec<Item>) -> f64 {
    let mut total_value = 0_f64;

    items.sort_by(|a, b| a.value_per_unit().partial_cmp(&b.value_per_unit()).unwrap());
    items.reverse();

    for item in items {
        if w == 0 {
            break;
        }
        let weight_moving = w.min(item.weight);
        total_value += item.value as f64 * (weight_moving as f64 / item.weight as f64);
        w -= weight_moving;
    }
    total_value
}

fn format(n: f64) -> String {
    format!("{:.*}", 4, n)
}

#[test]
fn test_maximum_of_the_loot() {
    assert_eq!(
        "180.0000",
        format(maximum_of_the_loot(
            50,
            vec![Item::new(60, 20), Item::new(100, 50), Item::new(120, 30)],
        ))
    );

    assert_eq!(
        "166.6667",
        format(maximum_of_the_loot(10, vec![Item::new(500, 30)])),
    );
}
