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

    // イテレータの rev() を使うパターン
    let vec = vec![1, 2, 3];
    let mut iter = vec.iter().rev();
    assert_eq!(&3, iter.next().unwrap());
    assert_eq!(&2, iter.next().unwrap());
    assert_eq!(&1, iter.next().unwrap());
}

#[test]
fn chunk() {
    let vec = vec!['a', 'b', 'c', 'd', 'e', 'f', 'g'];
    let mut iter = vec.chunks(2);
    assert_eq!(iter.next().unwrap(), &['a', 'b']);
    assert_eq!(iter.next().unwrap(), &['c', 'd']);
    assert_eq!(iter.next().unwrap(), &['e', 'f']);
    assert_eq!(iter.next().unwrap(), &['g']);
    assert_eq!(iter.next(), None);
}

#[test]
fn take() {
    let vec = vec!['a', 'b', 'c', 'd', 'e', 'f', 'g'];

    let take = vec
        .iter()
        .take(3)
        .map(|v| {
            format!("take: {}", v)
        })
        .collect::<Vec<String>>();

    assert_eq!(take, vec!["take: a", "take: b", "take: c"]);
}