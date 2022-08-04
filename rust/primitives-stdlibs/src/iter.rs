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

#[test]
fn filter_map() {
    println!("/// filter_map ///");
    // filter_map
    // https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.filter_map
    let data = ["foo".to_owned(), "bar".to_owned(), "baz".to_owned()];
    let mut r = data.iter().filter_map(|d| {
        if d == "bar" {
            Some(format!("{}!!!", d))
        } else {
            None
        }
    });

    println!("{:?}", r);
    assert_eq!(Some("bar!!!".to_owned()), r.next());
    assert_eq!(None, r.next());
}

#[test]
#[allow(clippy::flat_map_identity)]
fn flatten() {
    // flatten
    // https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.flatten
    // ｛イテレータを返すイテレータ｝に対して、｛返されたイテレータを繋げたイテレータ｝を返す
    let iter = vec![vec![0, 1, 2], vec![3, 4]].into_iter();

    println!("{:?}", iter.clone().flatten().collect::<Vec<_>>()); // [0, 1, 2, 3, 4]

    // `flatten()` は、 `.flat_map(|x| x)` と同等
    assert_eq!(
        iter.clone().flatten().collect::<Vec<_>>(),
        iter.flat_map(|x| x).collect::<Vec<_>>(),
    );
}

// イテレータの残りの要素を取る
#[test]
fn take_remains_from_iter() {
    let nums = vec![0, 1, 2, 3, 4, 5];
    for (i, n) in nums.iter().enumerate() {
        println!("i: {}, n: {}", i, n);

        if i == 3 {
            // `i: 3` 番目の要素以降を取得する
            println!("{:?}", nums.get(i..));
        }
    }
    // i: 0, n: 0
    // i: 1, n: 1
    // i: 2, n: 2
    // i: 3, n: 3
    // Some([3, 4, 5])
    // i: 4, n: 4
    // i: 5, n: 5
}

#[test]
fn max() {
    let nums = vec![1, 5, 2, 8, 3];
    assert_eq!(nums.iter().max(), Some(&8));
}

// Returning Rust Iterators | Depth-First
// https://depth-first.com/articles/2020/06/22/returning-rust-iterators/#simpleiteratordelegation
mod returning_iterator {

    // Associated Type
    mod associated_type {
        trait Container<'a> {
            type ItemIterator: Iterator<Item = &'a u8>;

            fn items(&'a self) -> Self::ItemIterator;
        }

        struct VecContainer {
            items: Vec<u8>,
        }

        impl<'a> Container<'a> for VecContainer {
            type ItemIterator = std::slice::Iter<'a, u8>;

            fn items(&'a self) -> Self::ItemIterator {
                self.items.iter()
            }
        }

        #[test]
        fn test() {
            let vec_container = VecContainer {
                items: vec![1, 2, 3],
            };

            // イテレータを返す items() を呼び出す
            let iter = vec_container.items();
            for i in iter {
                println!("{}", i);
            }
        }
    }
}
