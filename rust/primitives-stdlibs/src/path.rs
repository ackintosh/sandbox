#[test]
fn path() {
    let mut current_dir = std::env::current_dir().unwrap();
    println!("current_dir: {:?}", current_dir);

    println!("file_name: {:?}", current_dir.file_name());
    println!("pop: {:?}", current_dir.pop());
    println!("current_dir: {:?}", current_dir);
}
