fn main() {
    let mut input = read_line(read_num());
    if majority_element(&mut input) {
        print!("1");
    } else {
        print!("0");
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

fn majority_element(input: &mut Vec<u64>) -> bool {
    let len = input.len();
    merge_sort(input, 0, len - 1);

    let more_than_half = len / 2 + 1;

    let mut n = input.first().unwrap() + 1;
    let mut count = 0;
    for i in input {
        if *i == n {
            count += 1;
        } else {
            n = *i;
            count = 1;
        }

        if count >= more_than_half {
            return true;
        }
    }

    false
}

fn merge_sort(input: &mut Vec<u64>, l: usize, r: usize) {
    if l >= r {
        return;
    }
    let m = (l + r) / 2;

    merge_sort(input, l, m);
    merge_sort(input, m + 1, r);
    merge(input, l, m, r);
}

fn merge(input: &mut Vec<u64>, l: usize, m: usize, r: usize) {
    let left = {
        let mut v = vec![];
        for i in l..=m {
            v.push(input[i]);
        }
        v
    };

    let right = {
        let mut v = vec![];
        for i in (m + 1)..=r {
            v.push(input[i]);
        }
        v
    };

    let mut index_input = l;
    let mut index_left = 0;
    let mut index_right = 0;

    while index_left <= left.len() - 1 && index_right <= right.len() - 1 {
        if left[index_left] <= right[index_right] {
            input[index_input] = left[index_left];
            index_left += 1;
        } else {
            input[index_input] = right[index_right];
            index_right += 1;
        }
        index_input += 1;
    }

    while index_left <= left.len() - 1 {
        input[index_input] = left[index_left];
        index_left += 1;
        index_input += 1;
    }

    while index_right <= right.len() - 1 {
        input[index_input] = right[index_right];
        index_right += 1;
        index_input += 1;
    }
}

mod test {
    use crate::{majority_element, merge, merge_sort};

    #[test]
    fn test_majority_element() {
        {
            let mut input = vec![2, 3, 9, 2, 2];
            let result = majority_element(&mut input);
            assert!(result);
        }
        {
            let mut input = vec![1, 2, 3, 4];
            let result = majority_element(&mut input);
            assert!(!result);
        }
    }

    #[test]
    fn test_merge_sort() {
        let mut input = vec![2, 3, 1, 5, 4];
        let r = input.len() - 1;
        merge_sort(&mut input, 0, r);
        assert_eq!(vec![1, 2, 3, 4, 5], input);
    }

    #[test]
    fn test_merge() {
        let mut input = vec![5, 6, 1, 2, 3, 4];
        let r = input.len() - 1;
        merge(&mut input, 0, 1, r);
        assert_eq!(vec![1, 2, 3, 4, 5, 6], input);
    }
}
