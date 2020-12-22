#[test]
fn test() {
    let n = 4i32 / 2i32;
    assert_eq!(n, 2);

    // i32 として扱われる
    let n = 3 / 2;
    // 小数点以下が切り捨てられる
    assert_eq!(n, 1);

    let n = 3f32 / 2f32;
    assert_eq!(n, 1.5);
    println!("{:?}", n);
}