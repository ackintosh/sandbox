#[test]
fn fold() {
    let vec = [1, 2, 3];
    let sum: i32 = vec.iter().fold(0, |a, &b| a.checked_add(b).unwrap());

    assert_eq!(sum, 6);
}
