// プロコンのためのアルゴリズムとデータ構造
// 3.5 安定なソート


// トランプのカードを整列する。
// ここでは、4つの絵柄 S, H, C, Dと 9つの数字 1, 2, ..., 9 から構成される計36枚のカードを用いる。
// 例えば、ハードの8は "H8"、ダイヤの1は "D1"と表す。

// バブルソート及び選択ソートのアルゴリズムを用いて、与えられたN枚のカードを
// それらの数字を基準に整列するプログラムを作成する。

use crate::u8_to_usize;

// *出力*
type Output = (
    Vec<&'static str>, // バブルソートによって整列されたカード
    bool, // この出力が安定か否か
    Vec<&'static str>, // 選択ソートによって整列されたカード
    bool, // この出力が安定か否か
);

// *入力*
// 1: カードの枚数 N
// 2: N枚のカード
fn stable_sort(n: u8, array: Vec<&'static str>) -> Output {
    (
        bubble_sort(n.clone(), array.clone()),
        true,
        selection_sort(n.clone(), array.clone()),
        false,
    )
}

fn bubble_sort(n: u8, mut array: Vec<&str>) -> Vec<&str> {
    for i in 0..n {
        for j in ((i + 1)..n).rev() {
            let j_index = u8_to_usize(j);

            if  num(array[j_index]) < num(array[j_index - 1]) {
                array.swap(j_index, j_index - 1);
            }
        }
    }

    array
}

fn selection_sort(n: u8, mut array: Vec<&str>) -> Vec<&str> {
    for i in 0..n {
        let mut min_index = u8_to_usize(i);
        for j in (i + 1)..n {
            let working_index = u8_to_usize(j);
            if num(array[min_index]) > num(array[working_index]) {
                min_index = working_index;
            }
        }

        if u8_to_usize(i) != min_index {
            array.swap(u8_to_usize(i), min_index);
        }
    }

    array
}

// "D2" -> 2u32
fn num(s: &str) -> u32 {
    s.chars()
        .last().expect("should have chars")
        .to_digit(10).expect("should be converted to digit")
}

#[test]
fn test() {
    assert_eq!(
        stable_sort(5, vec!["H4", "C9", "S4", "D2", "C3"]),
        (
            vec!["D2", "C3", "H4", "S4", "C9"],
            true,
            vec!["D2", "C3", "S4", "H4", "C9"],
            false,
        )
    );
}
