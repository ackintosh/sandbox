use std::collections::HashMap;

fn main() {
    let n = read_num();
    let (number_of_operations, sequence) = primitive_calculator(n);
    println!("{}", number_of_operations);
    println!(
        "{}",
        sequence
            .iter()
            .map(|n| n.to_string())
            .collect::<Vec<_>>()
            .join(" ")
    );
}

fn read_num() -> u32 {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    buff.trim().parse::<u32>().unwrap()
}

// output:
//   - minimum number of operations
//   - a sequence of intermediate numbers
fn primitive_calculator(n: u32) -> (u32, Vec<u32>) {
    let mut sequences: HashMap<u32, Vec<u32>> = HashMap::new();
    let mut minimum_numbers: HashMap<u32, u32> = HashMap::new();
    let mut working_n = 1;
    // the number n starting from 1.
    sequences.insert(1, vec![1]);
    minimum_numbers.insert(1, 0);

    while working_n < n {
        let mut insert_sequence = |n: u32| {
            let mut seq = sequences.get(&working_n).unwrap().clone();
            seq.push(n);
            sequences.insert(n, seq);
        };

        let operations_n = { *minimum_numbers.get(&working_n).unwrap() };
        if let Some(added) = working_n.checked_add(1) {
            match minimum_numbers.get(&added) {
                None => {
                    minimum_numbers.insert(added, operations_n + 1);
                    insert_sequence(added);
                }
                Some(a) => {
                    if *a > operations_n + 1 {
                        minimum_numbers.insert(added, operations_n + 1);
                        insert_sequence(added);
                    }
                }
            }
        }

        if let Some(doubled) = working_n.checked_mul(2) {
            match minimum_numbers.get(&doubled) {
                None => {
                    minimum_numbers.insert(doubled, operations_n + 1);
                    insert_sequence(doubled);
                }
                Some(a) => {
                    if *a > operations_n + 1 {
                        minimum_numbers.insert(doubled, operations_n + 1);
                        insert_sequence(doubled);
                    }
                }
            }
        }

        if let Some(tripled) = working_n.checked_mul(3) {
            match minimum_numbers.get(&tripled) {
                None => {
                    minimum_numbers.insert(tripled, operations_n + 1);
                    insert_sequence(tripled);
                }
                Some(a) => {
                    if *a > operations_n + 1 {
                        minimum_numbers.insert(tripled, operations_n + 1);
                        insert_sequence(tripled);
                    }
                }
            }
        }
        working_n += 1;
    }

    (
        *minimum_numbers.get(&n).unwrap(),
        sequences.get(&n).unwrap().clone(),
    )
}

#[test]
fn test_primitive_calculator() {
    assert_eq!((0, vec![1]), primitive_calculator(1));
    assert_eq!((3, vec![1, 2, 4, 5]), primitive_calculator(5));
    assert_eq!(
        (
            14,
            vec![1, 3, 9, 10, 11, 22, 66, 198, 594, 1782, 5346, 16038, 16039, 32078, 96234]
        ),
        primitive_calculator(96234)
    );
}
