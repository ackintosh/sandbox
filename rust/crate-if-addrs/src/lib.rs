#[test]
fn test() {
    let interfaces = if_addrs::get_if_addrs().unwrap();

    for i in interfaces.iter() {
        println!("{:?}", i);
    }
}