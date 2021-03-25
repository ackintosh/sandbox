#[test]
fn vector() {
    let vec = vec![1, 2, 3];

    assert_eq!(vec.len(), 3);
    assert_eq!(vec[0usize], 1);
    assert_eq!(vec[2usize], 3);
}

#[test]
fn initialize() {
    // 要素数3, 各要素はi32の最大値を持つベクターを作る
    let n = 3;
    let vec = vec![i32::max_value(); n];
    println!("{:?}", vec);
}

#[test]
fn append() {
    {
        let mut vec = vec![1, 2, 3];
        let mut other = vec![4, 5, 6];
        vec.append(&mut other);

        assert_eq!(vec, vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(other, vec![]);
    }

    // otherが空の場合
    {
        let mut vec = vec![1, 2, 3];
        let mut other = vec![];
        vec.append(&mut other);

        assert_eq!(vec, vec![1, 2, 3]);
        assert_eq!(other, vec![]);
    }
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

#[test]
fn clear() {
    let mut vec = vec![1, 2, 3];
    assert_eq!(vec.len(), 3);
    println!("{:?}", vec);

    vec.clear();
    assert_eq!(vec.len(), 0);
    println!("{:?}", vec);
}

mod index {
    use std::ops::Index;

    // 特定のindexの値を取る
    #[test]
    fn get_value_at_index() {
        let vec = vec!["a", "b", "c"];
        let str = vec.index(2);
        println!("{:?}", str);
        // "c"

        // 範囲外の要素にアクセスするとpanic
        // index out of bounds: the len is 3 but the index is 999
        // let _ = vec.index(999);
    }

    // 特定の値を持つ(最初の)indexを取る
    #[test]
    fn position() {
        let vec = vec!["a", "b", "c"];
        let index = vec.iter().position(|&str| str == "b").unwrap();
        assert_eq!(index, 1_usize);
    }
}

mod update {
    // 参照渡しで各要素を更新する
    #[test]
    fn pass_by_reference() {
        let mut vec = vec![1, 2, 3];
        plus_10(&mut vec);

        println!("{:?}", vec);
        // [11, 12, 13]
    }

    #[test]
    fn multi_dimension() {
        let mut vec = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];

        vec.iter_mut().for_each(|row| {
            plus_10(row);
        });

        println!("{:?}", vec);
        // [[11, 12, 13], [14, 15, 16], [17, 18, 19]]
    }

    // 特定の要素のみを更新する
    #[test]
    fn particular_element() {
        let mut vec = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];

        let target_row = 1;
        let target_column = 2;

        match vec.get_mut(target_row) {
            Some(column) => match column.get_mut(target_column) {
                Some(target) => {
                    *target += 10;
                }
                None => unreachable!(),
            },
            None => unreachable!(),
        }

        println!("{:?}", vec);
        // [[1, 2, 3], [4, 5, 16], [7, 8, 9]]
    }

    fn plus_10(vec: &mut Vec<i32>) {
        vec.iter_mut().for_each(|v| {
            *v += 10;
        });
    }
}

mod find {
    // ベクターの最大値とそのインデックスを取る
    #[test]
    fn position_max() {
        let vec = vec![1, 2, 3];
        let mut max_num = 0;
        let mut max_index = 0;
        vec.iter().enumerate().for_each(|(index, &n)| {
            if max_num < n {
                max_num = n;
                max_index = index;
            }
        });

        assert_eq!(max_num, 3);
        assert_eq!(max_index, 2);
    }
}
