// アルゴリズムイントロダクション 4. 分割統治

// 出力:
//   - 最大部分配列の開始インデックス
//   - 最大部分配列の終了インデックス
//   - 最大部分配列に属する要素の和
fn find_max_subarray(input: &Vec<i8>, low: usize, high: usize) -> (usize, usize, i8) {
    println!("*** find_max_subarray ***");
    println!("input: {:?} \nlow: {} \nhigh: {}", input, low, high);

    if low == high {
        return (low, high, input[low]);
    }

    let mid = (high + low) / 2;
    let (left_low, left_high, left_sum) = find_max_subarray(input, low, mid);
    let (right_low, right_high, right_sum) = find_max_subarray(input, mid + 1, high);
    let (crossing_low, crossing_high, crossing_sum) = find_max_crossing_subarray(input, low, high);

    if left_sum >= right_sum && left_sum >= crossing_sum {
        (left_low, left_high, left_sum)
    } else if right_sum >= left_sum && right_sum >= crossing_sum {
        (right_low, right_high, right_sum)
    } else {
        (crossing_low, crossing_high, crossing_sum)
    }
}

fn find_max_crossing_subarray(input: &Vec<i8>, low: usize, high: usize) -> (usize, usize, i8) {
    let mid = (high + low) / 2; // usize同士の除算なので切り捨てになる
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
    input: &Vec<i8>,
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
    // "中央点を跨ぐ" ので、midからlowに向かって探索する
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
    // "中央点を跨ぐ" ので、mid+1からhighに向かって探索する
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
    use crate::algorithms::find_max_subarray::{find_max_crossing_subarray, find_max_subarray};

    #[test]
    fn test_find_max_subarray() {
        let input = vec![
            13, -3, -25, 20, -3, -16, -23, 18, 20, -7, 12, -5, -22, 15, -4, 7,
        ];
        let high = input.len() - 1;
        let output = find_max_subarray(&input, 0, high);
        assert_eq!(7, output.0);
        assert_eq!(10, output.1);
        assert_eq!(43, output.2);
    }

    #[test]
    fn test_find_max_crossing_subarray() {
        let input = vec![
            13, -3, -25, 20, -3, -16, -23, 18, 20, -7, 12, -5, -22, 15, -4, 7,
        ];
        let high = input.len() - 1;
        let output = find_max_crossing_subarray(&input, 0, high);
        assert_eq!(7, output.0);
        assert_eq!(10, output.1);
        assert_eq!(43, output.2);
    }
}
