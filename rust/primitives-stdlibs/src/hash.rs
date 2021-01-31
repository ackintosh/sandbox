use std::collections::HashMap;

#[test]
fn insert() {
    let mut contacts = HashMap::new();
    contacts.insert("Daniel", "789-1234");
    contacts.insert("Ashley", "123-1238");

    println!("{:?}", contacts);

    contacts.insert("test", "000-0000");
    contacts.insert("test", "000-0000");
    println!("{:?}", contacts);

    // testの値が上書きされる
    contacts.insert("test", "999-9999");
    println!("{:?}", contacts);
}

#[test]
fn max_by() {
    let mut contacts = HashMap::new();
    contacts.insert("key1", 100);
    contacts.insert("key2", 200);
    contacts.insert("key3", 300);

    let max = contacts.iter().max_by(|a, b| a.1.cmp(b.1)).unwrap();
    assert_eq!(max.1, &300);
}
