// https://www.coursera.org/learn/algorithmic-toolbox/programming/w9YDz/programming-assignment-4-divide-and-conquer/instructions

use std::cmp::Ordering;

fn main() {
    let a = read_line(read_num());
    let b = read_line(read_num());

    let result = search(&a, &b)
        .iter()
        .map(|res| match res {
            None => "-1".to_owned(),
            Some(n) => format!("{}", n),
        })
        .collect::<Vec<_>>();
    print!("{}", result.join(" "));
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

fn search(a: &Vec<u64>, b: &Vec<u64>) -> Vec<Option<usize>> {
    b.iter()
        .map(|target| binary_search(a, 0, a.len() - 1, target))
        .collect()
}

// 二分探索
// 値の重複がある場合は、最も先頭にあるインデックスを返す
fn binary_search(input: &Vec<u64>, l: usize, r: usize, target: &u64) -> Option<usize> {
    if l > r {
        return None;
    }

    let m = (l + r) / 2;

    match input[m].cmp(target) {
        Ordering::Less => binary_search(input, m + 1, r, target),
        Ordering::Equal => {
            let mut tmp = m;
            let mut result = m;
            while input[tmp] == *target {
                result = tmp;
                if tmp == 0 {
                    break;
                }
                tmp -= 1;
            }
            Some(result)
        }
        Ordering::Greater => binary_search(input, l, m - 1, target),
    }
}

mod test {
    use crate::{binary_search, search};

    #[test]
    fn test_binary_search() {
        let input = vec![1, 5, 8, 12, 13];
        assert_eq!(Some(0), binary_search(&input, 0, input.len() - 1, &1));
        assert_eq!(Some(1), binary_search(&input, 0, input.len() - 1, &5));
        assert_eq!(Some(4), binary_search(&input, 0, input.len() - 1, &13));
        assert_eq!(None, binary_search(&input, 0, input.len() - 1, &99));
    }

    #[test]
    fn test_search() {
        let result = search(&vec![1, 5, 8, 12, 13], &vec![8, 1, 23, 1, 11]);
        assert_eq!(vec![Some(2), Some(0), None, Some(0), None], result);
    }

    #[test]
    fn test_duplicates() {
        let result = search(&vec![2, 4, 4, 4, 7, 7, 9], &vec![9, 4, 5, 2]);
        assert_eq!(vec![Some(6), Some(1), None, Some(0)], result);
    }
}
