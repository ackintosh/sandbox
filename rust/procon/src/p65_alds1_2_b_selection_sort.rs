// プロコンのためのアルゴリズムとデータ構造
// 3.4 選択ソート

use crate::u8_to_usize;

// *出力*
// 要素1: 整列された数列
// 要素2: ソートで行われた交換回数
type Output = (Vec<u8>, u8);

// *入力*
// 1: 数列の長さを表す整数N
// 2: N個の数列
fn selection_sort(n: u8, mut array: Vec<u8>) -> Output {
    // ソートで行われた交換回数
    let mut num_of_swapped = 0;

    for i in 0..n {
        let mut min_index = u8_to_usize(i);
        for ii in i..n {
            let working_index = u8_to_usize(ii);
            if array[working_index] < array[min_index] {
                min_index = working_index;
            }
        }

        let i_index = u8_to_usize(i);
        if i_index != min_index {
            array.swap(u8_to_usize(i), min_index);
            num_of_swapped += 1;
        }
    }
    (array, num_of_swapped)
}

#[test]
fn test() {
    assert_eq!(
        selection_sort(6, vec![5, 6, 4, 2, 1, 3]),
        (vec![1, 2, 3, 4, 5, 6], 4)
    );
}
