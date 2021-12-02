// * アルゴリズム イントロダクション 2章 P.26
// * Rust実装の手本: https://github.com/TheAlgorithms/Rust/blob/master/src/sorting/merge_sort.rs

fn merge(input: &mut Vec<u8>, p: usize, q: usize, r: usize) {
    let left = {
        let mut v = vec![];
        for i in p..=q {
            v.push(input[i]);
        }
        v
    };

    let right = {
        let mut v = vec![];
        for i in (q + 1)..=r {
            v.push(input[i]);
        }
        v
    };

    let mut left_index = 0;
    let mut right_index = 0;
    let mut input_index = p;

    while left_index < left.len() && right_index < right.len() {
        if left[left_index] < right[right_index] {
            input[input_index] = left[left_index];
            left_index += 1;
        } else {
            input[input_index] = right[right_index];
            right_index += 1;
        }
        input_index += 1;
    }

    while left_index < left.len() {
        input[input_index] = left[left_index];
        left_index += 1;
    }

    while right_index < right.len() {
        input[input_index] = right[right_index];
        right_index += 1;
    }
}

fn merge_sort(input: &mut Vec<u8>, p: usize, r: usize) {
    if p >= r {
        return;
    }
    let q = (r + p) / 2;
    merge_sort(input, p, q);
    merge_sort(input, q + 1, r);
    merge(input, p, q, r);
}

mod test {
    use crate::algorithms::merge_sort::{merge, merge_sort};

    #[test]
    fn test_merge() {
        let mut input = vec![1, 3, 5, 2, 4, 6];
        merge(&mut input, 0, 2, 5);
        assert_eq!(vec![1, 2, 3, 4, 5, 6], input);
    }

    #[test]
    fn test_merge_sort() {
        let mut input = vec![5, 2, 4, 6, 1, 3];
        merge_sort(&mut input, 0, 5);
        assert_eq!(vec![1, 2, 3, 4, 5, 6], input);
    }
}
