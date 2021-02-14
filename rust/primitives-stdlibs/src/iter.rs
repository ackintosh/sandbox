#[test]
fn fold() {
    let vec = [1, 2, 3];
    let sum: i32 = vec.iter().fold(0, |a, &b| a.checked_add(b).unwrap());

    assert_eq!(sum, 6);
}

#[test]
#[allow(clippy::iter_nth_zero)]
fn nth() {
    let vec = [1, 2, 3];
    let mut iter = vec.iter();

    // nth() は要素を消費する
    assert_eq!(iter.nth(0), Some(&1));
    assert_eq!(iter.nth(0), Some(&2));
    assert_eq!(iter.nth(0), Some(&3));
    assert_eq!(iter.nth(0), None);
}
