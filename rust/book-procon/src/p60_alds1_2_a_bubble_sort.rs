// プロコンのためのアルゴリズムとデータ構造
// 3.3 バブルソート

use crate::u8_to_usize;

// *出力*
// 要素1: 整列された数列
// 要素2: ソートで行われた交換回数
type Output = (Vec<u8>, u8);

// *入力*
// 1: 数列の長さを表す整数N
// 2: N個の数列
fn bubble_sort(n: u8, mut array: Vec<u8>) -> Output {
    // ソートで行われた交換回数
    let mut num_of_swapped = 0u8;

    let mut should_continue = true;
    let mut i = 0u8;

    while should_continue {
        should_continue = false;
        for j in ((i + 1)..n).rev() {
            let j = u8_to_usize(j);
            // println!("array[j]: {}, array[j - 1]: {}", array[j], array[j - 1]);

            if array[j] < array[j - 1] {
                array.swap(j, j - 1);
                num_of_swapped += 1;
                should_continue = true;
            }
        }
        i += 1;
    }

    (array, num_of_swapped)
}

#[test]
fn test() {
    assert_eq!(
        bubble_sort(5, vec![5, 3, 2, 4, 1]),
        (vec![1, 2, 3, 4, 5], 8)
    );
}
