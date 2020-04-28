// プロコンのためのアルゴリズムとデータ構造
// 3.2 挿入ソート
use std::convert::TryFrom;

fn insertion_sort(array: Vec<u8>, n: u8) -> Vec<Vec<u8>> {
    let mut a = array.clone();

    // ソートの途中経過も含めたvector群
    let mut result = vec![];
    result.push(a.clone());

    for i in 1..n {
        let mut j = i8::try_from(i).expect("should be converted to i8") - 1;

        let mut v = a[u8_to_usize(i)];

        // println!("i: {}, v: {}, a[i]: {}, a[j]: {}", i, v, a[u8_to_usize(i)], a[i8_to_usize(j)]);
        while j >= 0 && a[i8_to_usize(j)] > v {
            a[i8_to_usize(j + 1)] = a[i8_to_usize(j)];
            j -= 1;
        }
        a[i8_to_usize(j + 1)] = v;

        result.push(a.clone());
    }

    result
}

fn u8_to_usize(n: u8) -> usize {
    usize::try_from(n).expect("should be converted to usize")
}

fn i8_to_usize(n: i8) -> usize {
    usize::try_from(n).expect("should be converted to usize")
}

#[test]
fn test() {
    let a = vec![5, 2, 4, 6, 1, 3];
    let n = 6;

    assert_eq!(
        insertion_sort(a, n),
        vec![
            vec![5, 2, 4, 6, 1, 3],
            vec![2, 5, 4, 6, 1, 3],
            vec![2, 4, 5, 6, 1, 3],
            vec![2, 4, 5, 6, 1, 3],
            vec![1, 2, 4, 5, 6, 3],
            vec![1, 2, 3, 4, 5, 6],
        ]
    );
}
