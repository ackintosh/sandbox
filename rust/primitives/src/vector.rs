#[test]
fn vector() {
    let vec = vec![1, 2, 3];

    assert_eq!(vec.len(), 3);
    assert_eq!(vec[0usize], 1);
    assert_eq!(vec[2usize], 3);
}

#[test]
fn reverse() {
    let mut vec = vec![1, 2, 3];
    vec.reverse();

    // 順番が逆になる
    assert_eq!(vec![3, 2, 1], vec);

    // しかし pop() が返す要素の順番は変わらない
    assert_eq!(1, vec.pop().unwrap());
    assert_eq!(2, vec.pop().unwrap());
    assert_eq!(3, vec.pop().unwrap());

    let mut vec = vec![1, 2, 3];
    vec.reverse();
    // イテレータの順番は逆になる
    let mut iter = vec.iter();
    assert_eq!(&3, iter.next().unwrap());
    assert_eq!(&2, iter.next().unwrap());
    assert_eq!(&1, iter.next().unwrap());
}
