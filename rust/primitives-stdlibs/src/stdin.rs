#[allow(dead_code)]
fn read_line() {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    println!("{}", buff);
}

// $ cargo test stdin
// #[test]
// fn test() {
//     // read_line();
//     assert_eq!(123, read());
// }
