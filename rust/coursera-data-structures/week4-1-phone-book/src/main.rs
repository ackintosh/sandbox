// https://www.coursera.org/learn/data-structures/programming/Hpuiz/programming-assignment-3-hash-tables/instructions
use std::convert::TryFrom;

fn main() {
    let n = read_num();
    let operations = read_operations(n);
    // println!("{:?}", operations);

    let mut phone_book = PhoneBook::new();

    for operation in operations {
        match operation.first().expect("should have element").as_str() {
            "add" => {
                let number = operation[1].parse::<u32>().unwrap();
                phone_book.add(number, operation[2].to_string());
            }
            "find" => {
                let number = operation[1].parse::<u32>().unwrap();
                let name = phone_book.find(number);
                if name.is_empty() {
                    println!("not found");
                } else {
                    println!("{}", name);
                }
            }
            "del" => {
                let number = operation[1].parse::<u32>().unwrap();
                phone_book.del(number);
            }
            _ => unreachable!(),
        }
    }
}

fn read_num() -> u64 {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    buff.trim().parse::<u64>().unwrap()
}

fn read_operations(number_of_elements: u64) -> Vec<Vec<String>> {
    let mut operations: Vec<Vec<String>> = vec![];

    for _ in 0..number_of_elements {
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();

        let mut strs = buff
            .split_whitespace()
            .map(|s| String::from(s))
            .collect::<Vec<_>>();
        operations.push(strs);
    }

    operations
}

// All phone numbers consist of decimal digits, they don’t have leading zeros, and each of them has no more than 7 digits.
// All names are non-empty strings of latin letters, and each of them has length at most 15.
struct PhoneBook {
    cells: Vec<String>,
}

impl PhoneBook {
    fn new() -> Self {
        Self {
            cells: vec!["".to_string(); 10000000],
        }
    }

    fn add(&mut self, number: u32, name: String) {
        self.cells[usize::try_from(number).unwrap()] = name;
    }

    fn find(&self, number: u32) -> String {
        self.cells[usize::try_from(number).unwrap()].clone()
    }

    fn del(&mut self, number: u32) {
        self.cells[usize::try_from(number).unwrap()] = "".to_string();
    }
}

#[cfg(test)]
mod tests {
    use crate::PhoneBook;

    #[test]
    fn operations() {
        let mut p = PhoneBook::new();
        p.add(1, "test".into());

        assert_eq!("test".to_string(), p.find(1));
        assert_eq!("".to_string(), p.find(2));

        p.del(1);
        assert_eq!("".to_string(), p.find(1));
    }

    #[test]
    fn phone_book() {
        // Sample 1
        {
            let mut p = PhoneBook::new();
            p.add(911, "police".to_string());
            p.add(76213, "Mom".to_string());
            p.add(17239, "Bob".to_string());

            assert_eq!("Mom".to_string(), p.find(76213));
            assert_eq!("".to_string(), p.find(910));
            assert_eq!("police".to_string(), p.find(911));

            p.del(910);
            p.del(911);

            assert_eq!("".to_string(), p.find(911));
            assert_eq!("Mom".to_string(), p.find(76213));

            p.add(76213, "daddy".to_string());

            assert_eq!("daddy".to_string(), p.find(76213));
        }

        // Sample 2
        {
            let mut p = PhoneBook::new();
            assert_eq!("".to_string(), p.find(3839442));

            p.add(123456, "me".to_string());
            p.add(0, "granny".to_string());

            assert_eq!("granny".to_string(), p.find(0));
            assert_eq!("me".to_string(), p.find(123456));

            p.del(0);
            p.del(0);

            assert_eq!("".to_string(), p.find(0));
        }
    }
}
