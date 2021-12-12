// アルゴリズムイントロダクション 4. 分割統治

fn find_max_crossing_subarray(input: Vec<i8>, low: usize, high: usize) -> (usize, usize, i8) {
    let mid = (high - low) / 2; // usize同士の除算なので切り捨てになる
    _find_max_crossing_subarray(input, low, mid, high)
}

// "中央点を跨ぐ" 最大部分配列を求める関数
// 入力:
//   - input: 対象の配列
//   - low: 探索対象範囲の開始インデックス
//   - mid: 探索対象範囲の中央点インデックス
//   - high: 探索対象範囲の終了インデックス
// 出力:
//   - 最大部分配列の開始インデックス
//   - 最大部分配列の終了インデックス
//   - 最大部分配列に属する要素の和
fn _find_max_crossing_subarray(
    input: Vec<i8>,
    low: usize,
    mid: usize,
    high: usize,
) -> (usize, usize, i8) {
    println!("*** _find_max_crossing_subarray ***");
    println!(
        "input: {:?} \nlow: {} \nmid: {} \nhigh: {}",
        input, low, mid, high
    );

    // /////////////////////////////
    // "左側の" 最大部分配列を求める
    // /////////////////////////////
    // 探索中の部分配列に属する要素の和
    let mut sum: i8 = 0;
    // "左側の" 最大部分配列に属する要素の和
    let mut left_sum: i8 = i8::MIN;
    // "左側の" 最大部分配列の開始インデックス
    let mut left_index = 0;

    for i in (low..=mid).rev() {
        sum += input[i];
        if sum >= left_sum {
            left_sum = sum;
            left_index = i;
        }
    }

    // /////////////////////////////
    // "右側の" 最大部分配列を求める
    // /////////////////////////////
    // 探索中の部分配列に属する要素の和
    let mut sum: i8 = 0; // 左側の計算で使っていた変数を再度初期化する
                         // "右側の" 最大部分配列に属する要素の和
    let mut right_sum: i8 = i8::MIN;
    // "右側の" 最大部分配列の開始インデックス
    let mut right_index = mid + 1;

    for j in (mid + 1)..=high {
        sum += input[j];
        if sum >= right_sum {
            right_sum = sum;
            right_index = j;
        }
    }

    (left_index, right_index, left_sum + right_sum)
}

mod test {
    use crate::algorithms::find_max_subarray::find_max_crossing_subarray;

    #[test]
    fn test_find_max_crossing_subarray() {
        let input = vec![
            13, -3, -25, 20, -3, -16, -23, 18, 20, -7, 12, -5, -22, 15, -4, 7,
        ];
        let high = input.len() - 1;
        let output = find_max_crossing_subarray(input, 0, high);
        assert_eq!(7, output.0);
        assert_eq!(10, output.1);
        assert_eq!(43, output.2);
    }
}
