// プロコンのためのアルゴリズムとデータ構造
// 5.2 線形探索

#[test]
fn test_linear_search() {
    let s = vec![1, 2, 3, 4, 5];
    let t = vec![3, 4, 1];
    let mut output = 0;

    for tt in t.iter() {
        for ss in s.iter() {
            if tt == ss {
                output += 1;
            }
        }
    }

    assert_eq!(3, output);
}
