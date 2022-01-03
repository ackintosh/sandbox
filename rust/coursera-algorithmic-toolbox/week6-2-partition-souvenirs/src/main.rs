fn main() {
    let n = read_num();
    let input = read_line(n);

    if partition_souvenirs(input) {
        println!("1");
    } else {
        println!("0");
    }
}

fn read_num() -> u64 {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    buff.trim().parse::<u64>().unwrap()
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

fn partition_souvenirs(input: Vec<u64>) -> bool {
    if input.len() < 3 {
        return false;
    }

    let sum: u64 = input.iter().sum();
    if sum % 3 != 0 {
        return false;
    }

    let third_of_sum = sum / 3;
    let mut matrix = vec![vec![0; third_of_sum as usize + 1]; input.len() + 1];

    for i in 1..=input.len() {
        for j in 1..=third_of_sum as usize {
            if j == input[i - 1] as usize {
                matrix[i][j] = matrix[i - 1][j] + 1;
            } else if let Some(remaining_sum) = j.checked_sub(input[i - 1] as usize) {
                matrix[i][j] = matrix[i - 1][remaining_sum] + 1;
            } else {
                matrix[i][j] = matrix[i - 1][j];
            }
        }
    }

    // println!("{:?}", matrix);

    matrix[input.len()][third_of_sum as usize] >= 2
}

#[test]
fn test_partition_souvenirs() {
    assert!(!partition_souvenirs(vec![3, 3, 3, 3]));
    assert!(!partition_souvenirs(vec![40]));

    assert!(partition_souvenirs(vec![1, 1, 1]));
    assert!(partition_souvenirs(vec![3, 1, 1, 2, 2]));
    assert!(partition_souvenirs(vec![
        17, 59, 34, 57, 17, 23, 67, 1, 18, 2, 59
    ]));
    assert!(partition_souvenirs(vec![
        1, 2, 3, 4, 5, 5, 7, 7, 8, 10, 12, 19, 25
    ]));
}
