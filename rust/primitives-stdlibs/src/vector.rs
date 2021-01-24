#[test]
fn vector() {
    let vec = vec![1, 2, 3];

    assert_eq!(vec.len(), 3);
    assert_eq!(vec[0usize], 1);
    assert_eq!(vec[2usize], 3);
}

#[test]
fn multidimensional_vector() {
    let vec = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];

    // 愚直にindexを指定する
    // indexが範囲外の場合は panic
    assert_eq!(vec[1][2], 6);

    // エラーハンドリングする場合
    let d1 = vec.get(1);
    assert!(d1.is_some());
    assert_eq!(d1.unwrap().get(2), Some(&6));
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
        .map(|v| format!("take: {}", v))
        .collect::<Vec<String>>();

    assert_eq!(take, vec!["take: a", "take: b", "take: c"]);
}

#[test]
fn sum() {
    let vec = vec![1, 2, 3];
    let n = vec.iter().sum::<i32>();
    assert_eq!(n, 6);
}

#[test]
fn sort() {
    let mut vec = vec![1, 2, 3];
    vec.sort_unstable();

    // 昇順 (変わらない)
    assert_eq!(vec, vec![1, 2, 3]);
}
