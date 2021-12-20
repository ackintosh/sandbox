fn quick_sort(input: &mut Vec<u8>) {
    let r = input.len() - 1;
    _quick_sort(input, 0, r);
}

fn _quick_sort(input: &mut Vec<u8>, l: usize, r: usize) {
    if l >= r {
        return;
    }
    // let pivot = input.first().unwrap(); // TODO: randomize

    // let m = two_way(input, l, r);
    let (k, p) = three_way(input, l, r);

    if k != 0 {
        _quick_sort(input, l, k - 1);
    }
    _quick_sort(input, p + 1, r);
}

fn swap(input: &mut Vec<u8>, a: usize, b: usize) {
    let tmp = input[a];
    input[a] = input[b];
    input[b] = tmp;
}

// https://www.toptal.com/developers/sorting-algorithms/quick-sort-3-way
// left < pivot
// middle = pivot
// right > pivot
fn three_way(input: &mut Vec<u8>, l: usize, r: usize) -> (usize, usize) {
    let mut i = l;
    let mut k = l; // start of `right`
    let mut p = r; // start of `middle`

    // move the pivot to the tail of elements.
    //   -> r == pivot
    swap(input, l, r);

    while i < p {
        if input[i] == input[r] {
            swap(input, i, p - 1);
            p -= 1;
        } else if input[i] < input[r] {
            swap(input, i, k);
            k += 1;
            i += 1;
        } else {
            i += 1;
        }
    }

    let distance = p - k;
    for pp in p..=r {
        for d in 0..distance {
            swap(input, pp - d, pp - (d + 1));
        }
    }

    (k, p)
}

// TheAlgorithms: https://github.com/TheAlgorithms/Rust/blob/master/src/sorting/quick_sort.rs
// left <= pivot
// right > pivot
fn two_way(input: &mut Vec<u8>, l: usize, r: usize) -> usize{
    let mut m = l;
    for i in (l + 1)..=r {
        if input[i] <= input[l] {
            swap(input, i, m + 1);
            m += 1;
        }
    }

    swap(input, l, m);
    m
}

mod test {
    use crate::algorithms::quick_sort::{quick_sort, three_way, two_way};

    #[test]
    fn test_quick_sort() {
        let mut input = vec![5, 3, 1, 6, 9, 2];
        quick_sort(&mut input);
        assert_eq!(vec![1, 2, 3, 5, 6, 9], input);
    }

    #[test]
    fn test_quick_sort_with_duplicates() {
        let mut input = vec![2, 3, 9, 2, 2];
        quick_sort(&mut input);
        assert_eq!(vec![2, 2, 2, 3, 9], input);
    }

    #[test]
    fn test_three_way() {
        let mut input = vec![2, 3, 9, 2, 2];
        three_way(&mut input, 0, 4);
        assert_eq!(vec![2, 2, 2, 9, 3], input);
    }

    #[test]
    fn test_two_way() {
        let mut input = vec![3, 2, 9];
        two_way(&mut input, 0, 2);
        assert_eq!(vec![2, 3, 9], input);
    }
}
