// 参考:
// * アルゴリズム イントロダクション 2章 P.32 練習問題 2.3-5

use std::cmp::Ordering;

fn binary_search(input: &Vec<u8>, target: u8, start: usize, end: usize) -> Option<usize> {
    if start > end {
        return None;
    }
    let m = (start + end) / 2;
    match input[m].cmp(&target) {
        Ordering::Less => binary_search(input, target, m + 1, end),
        Ordering::Equal => Some(m),
        Ordering::Greater => binary_search(input, target, start, end - 1),
    }
}

#[test]
fn test_binary_search() {
    {
        let input = vec![1, 2];
        assert_eq!(Some(0), binary_search(&input, 1, 0, 1));
        assert_eq!(Some(1), binary_search(&input, 2, 0, 1));
        assert_eq!(None, binary_search(&input, 3, 0, 1));
    }
    {
        let input = vec![1, 2, 3];
        assert_eq!(Some(0), binary_search(&input, 1, 0, 2));
        assert_eq!(Some(1), binary_search(&input, 2, 0, 2));
        assert_eq!(Some(2), binary_search(&input, 3, 0, 2));
        assert_eq!(None, binary_search(&input, 4, 0, 2));
    }
}
