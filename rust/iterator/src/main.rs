fn main() {
    filter_map();
    flatten();
}

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

fn flatten() {
    println!("/// flatten ///");
    // flatten
    // https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.flatten
    let iter = vec![vec![0, 1, 2], vec![3, 4]].into_iter();

    println!("{:?}", iter.clone().flatten().collect::<Vec<_>>()); // [0, 1, 2, 3, 4]

    // .flat_map(|x| x) と同等
    assert_eq!(
        iter.clone()
            .flatten()
            .collect::<Vec<_>>(),
        iter.clone()
            .flat_map(|x| x)
            .collect::<Vec<_>>(),
    );
}
