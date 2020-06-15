// プロコンのためのアルゴリズムとデータ構造
// 5.3 二分探索

#[test]
fn test() {
    // 昇順に整列済み, 重複なし
    let arr = vec![1, 2, 3, 4, 5];

    assert!(binary_search(3, &arr));
    assert!(binary_search(1, &arr));
    assert!(binary_search(4, &arr));
    assert!(!binary_search(9, &arr));
}

fn binary_search(n: u32, arr: &Vec<u32>) -> bool {
    let mut left: usize = 0;
    let mut right: usize = arr.len() - 1;

    while left < right {
        let mid = (left + right) / 2;

        if arr[mid] == n {
            return true;
        } else if arr[mid] < n {
            left = mid + 1;
        } else {
            // arr[mid] > n
            right = mid - 1;
        }
    }

    return false;
}
