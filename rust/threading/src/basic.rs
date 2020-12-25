#[test]
fn test() {
    let handle = std::thread::spawn(|| {
        println!("Hello, world!");
    });

    dbg!(handle.join());
}
