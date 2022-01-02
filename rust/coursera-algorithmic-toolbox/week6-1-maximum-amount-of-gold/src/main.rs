// https://www.coursera.org/learn/algorithmic-toolbox/programming/nZrTS/programming-assignment-6-dynamic-programming-2/instructions

fn main() {
    // number_of_elements: 2
    //   - 1. the capacity W
    //   - 2. the number of bars of gold
    let line = read_line(2);
    let weight = line[0];
    let number_of_bars = line[1];

    let items = read_line(number_of_bars);

    println!("{}", maximum_amount_of_gold(weight, items));
}

fn read_line(number_of_elements: u64) -> Vec<u64> {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    let mut strs = buff.split_whitespace();

    let mut nums = vec![];
    for _ in 0..number_of_elements {
        nums.push(strs.next().unwrap().parse::<u64>().unwrap());
    }
    nums
}

fn maximum_amount_of_gold(weight: u64, items: Vec<u64>) -> u64 {
    let mut matrix = vec![vec![0_u64; weight as usize + 1]; items.len() + 1];

    for i in 1..=items.len() {
        for w in 1..=weight as usize {
            let a = matrix[i - 1][w];

            if let Some(sub) = (w as u64).checked_sub(items[i - 1]) {
                let b = matrix[i - 1][sub as usize] + (items[i - 1] as u64);
                matrix[i][w] = a.max(b);
            } else {
                matrix[i][w] = a;
            }
        }
    }

    // println!("{:?}", matrix);
    matrix[items.len()][weight as usize]
}

#[test]
fn test_maximum_amount_of_gold() {
    assert_eq!(9, maximum_amount_of_gold(10, vec![1, 4, 8]));
}
