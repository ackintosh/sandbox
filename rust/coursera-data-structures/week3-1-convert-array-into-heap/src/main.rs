// https://www.coursera.org/learn/data-structures/programming/Kru9d/programming-assignment-2-priority-queues-and-disjoint-sets

fn main() {
    let n = read_num();
    let mut nums = read_nums(n);
    let swaps = convert_array_into_heap(&mut nums);

    println!("{}", swaps.len());
    for swap in swaps {
        println!("{} {}", swap.0, swap.1);
    }
}

fn read_num() -> u64 {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    buff.trim().parse::<u64>().unwrap()
}

fn read_nums(number_of_elements: u64) -> Vec<u64> {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    let mut strs = buff.split_whitespace();

    let mut nums = vec![];
    for _ in 0..number_of_elements {
        nums.push(strs.next().unwrap().parse::<u64>().unwrap());
    }
    nums
}

// min-heap
fn convert_array_into_heap(array: &mut Vec<u64>) -> Vec<(usize, usize)> {
    let mut swaps = vec![];

    for i in (0..=(array.len() / 2)).into_iter().rev() {
        swaps.append(&mut sift_down(array, i));
    }

    swaps
}

fn sift_down(array: &mut Vec<u64>, i: usize) -> Vec<(usize, usize)> {
    let mut swaps = vec![];

    let child = smaller_child(array, i);
    // println!("sift_down: child: {:?}", child);

    match child {
        None => {}
        Some(child_index) => {
            if array[i] > array[child_index] {
                swaps.push((i, child_index));
                swap(array, i, child_index);
                let mut downstream_swaps = sift_down(array, child_index);
                swaps.append(&mut downstream_swaps);
            }
        }
    }

    // println!("sift_down: swaps: {:?}", swaps);
    swaps
}

fn swap(array: &mut Vec<u64>, a: usize, b: usize) {
    let tmp = array[a];
    array[a] = array[b];
    array[b] = tmp;
}

fn smaller_child(array: &mut Vec<u64>, i: usize) -> Option<usize> {
    let left = left_child(array, i);
    let right = right_child(array, i);

    match (left, right) {
        (None, None) => None,
        (Some(left_index), None) => Some(left_index),
        (None, Some(right_index)) => Some(right_index),
        (Some(left_index), Some(right_index)) => {
            if array[left_index] < array[right_index] {
                Some(left_index)
            } else {
                Some(right_index)
            }
        }
    }
}

fn left_child(array: &Vec<u64>, i: usize) -> Option<usize> {
    let left = 2 * i + 1;

    if array.len() > left {
        Some(left)
    } else {
        None
    }
}

fn right_child(array: &Vec<u64>, i: usize) -> Option<usize> {
    let right = 2 * i + 2;

    if array.len() > right {
        Some(right)
    } else {
        None
    }
}

#[test]
fn test_convert_array_into_heap() {
    {
        let mut array = vec![5, 4, 3, 2, 1];
        let swaps = convert_array_into_heap(&mut array);
        assert_eq!(vec![1, 2, 3, 5, 4], array);
        assert_eq!(vec![(1, 4), (0, 1), (1, 3)], swaps);
    }
    {
        let mut array = vec![1, 2, 3, 4, 5];
        let swaps = convert_array_into_heap(&mut array);
        assert_eq!(vec![1, 2, 3, 4, 5], array);
        assert!(swaps.is_empty());
    }
}

#[test]
fn test_sift_down() {
    let mut array = vec![1, 2, 3];
    let swaps = sift_down(&mut array, 0);

    assert_eq!(vec![3, 2, 1], array);
    assert_eq!(vec![(0, 2)], swaps);
}

#[test]
fn test_swap() {
    let mut array = vec![1, 2, 3];
    swap(&mut array, 0, 1);
    assert_eq!(vec![2, 1, 3], array);
}

#[test]
fn test_child_index() {
    let array = vec![5, 4, 3, 2, 1];
    assert_eq!(Some(1), left_child(&array, 0));
    assert_eq!(Some(2), right_child(&array, 0));
    assert_eq!(Some(3), left_child(&array, 1));
    assert_eq!(Some(4), right_child(&array, 1));
    assert_eq!(None, left_child(&array, 2));
    assert_eq!(None, right_child(&array, 2));
}
