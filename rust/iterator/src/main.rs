fn main() {
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
