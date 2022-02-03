// https://www.coursera.org/learn/data-structures/programming/Hpuiz/programming-assignment-3-hash-tables/instructions
use std::collections::VecDeque;
use std::convert::TryFrom;

fn main() {
    let cardinality = read_num::<u32>();
    let mut hash_table = HashTable::new(cardinality);

    let number_of_elements = read_num::<u32>();
    let operations = read_operations(number_of_elements);

    for operation in operations {
        match operation.first().expect("should have element").as_str() {
            "add" => {
                let string = operation.get(1).expect("should have string");
                hash_table.add(string.clone());
            }
            "del" => {
                let string = operation.get(1).expect("should have string");
                hash_table.del(string);
            }
            "find" => {
                let string = operation.get(1).expect("should have string");
                if hash_table.find(string) {
                    println!("yes");
                } else {
                    println!("no");
                }
            }
            "check" => {
                let i = operation
                    .get(1)
                    .expect("should have index")
                    .parse::<usize>()
                    .unwrap();
                match hash_table.check(i) {
                    None => println!(),
                    Some(chain) => {
                        for c in chain {
                            print!("{} ", c)
                        }
                        println!();
                    }
                };
            }
            _ => unreachable!(),
        }
    }
}

fn read_num<T>() -> T
where
    T: std::str::FromStr,
    <T as std::str::FromStr>::Err: std::fmt::Debug, // https://stackoverflow.com/questions/67352894/rust-error-conversion-for-generic-fromstr-unwrap-errors-out-with-unsatisfied-tr
{
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    buff.trim().parse::<T>().unwrap()
}

fn read_operations(number_of_elements: u32) -> Vec<Vec<String>> {
    let mut operations: Vec<Vec<String>> = vec![];

    for _ in 0..number_of_elements {
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();

        let strs = buff
            .split_whitespace()
            .map(|s| String::from(s))
            .collect::<Vec<_>>();
        operations.push(strs);
    }

    operations
}

struct HashTable {
    cardinality: u32,
    chains: Vec<VecDeque<String>>,
}

impl HashTable {
    fn new(cardinality: u32) -> Self {
        let size = usize::try_from(cardinality).unwrap();

        Self {
            cardinality,
            chains: vec![VecDeque::new(); size],
        }
    }

    fn add(&mut self, s: String) {
        let hash_as_index = usize::try_from(hash(&s, self.cardinality)).unwrap();
        let chain: &mut VecDeque<String> = self
            .chains
            .get_mut(hash_as_index)
            .expect("should have a chain");

        if chain.contains(&s) {
            return;
        } else {
            chain.push_front(s);
        }
    }

    fn del(&mut self, s: &String) {
        let hash_as_index = usize::try_from(hash(s, self.cardinality)).unwrap();

        match self.chains.get_mut(hash_as_index) {
            None => {}
            Some(chain) => {
                match chain.iter().position(|string| string == s) {
                    None => {}
                    Some(index) => {
                        chain.remove(index);
                    }
                };
            }
        };
    }

    fn find(&self, s: &String) -> bool {
        let hash_as_index = usize::try_from(hash(&s, self.cardinality)).unwrap();

        match self.chains.get(hash_as_index) {
            None => false,
            Some(chain) => chain.contains(s),
        }
    }

    fn check(&self, i: usize) -> Option<&VecDeque<String>> {
        self.chains.get(i)
    }
}

// PolyHash(S, p, x)
fn hash(s: &String, m: u32) -> u32 {
    let p = 1_000_000_007;
    let x = 263;

    let mut hash = 0_u64;

    for c in s.chars().rev() {
        hash = ((hash * x) + c as u64) % p;
    }

    hash as u32 % m
}

#[cfg(test)]
mod tests {
    use super::hash;
    use crate::HashTable;
    use std::collections::VecDeque;

    #[test]
    fn test_hash() {
        assert_eq!(97, hash(&"a".to_string(), 100));
        assert_eq!(4, hash(&"world".to_string(), 5));
        assert_eq!(4, hash(&"HellO".to_string(), 5));
    }

    #[test]
    fn hash_table() {
        let mut hash_table = HashTable::new(5);
        assert!(!hash_table.find(&"test".to_string()));

        hash_table.add("test".to_string());
        assert!(hash_table.find(&"test".to_string()));

        hash_table.del(&"test".to_string());
        assert!(!hash_table.find(&"test".to_string()));

        hash_table.add("HellO".to_string());
        hash_table.add("world".to_string());
        let mut expected = VecDeque::new();
        expected.push_front("HellO".to_string());
        expected.push_front("world".to_string());
        assert_eq!(Some(&expected), hash_table.check(4));
    }
}
