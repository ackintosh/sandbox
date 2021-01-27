use std::collections::HashMap;

#[test]
fn test() {
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
