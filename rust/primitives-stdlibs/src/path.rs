use std::path::PathBuf;

#[test]
fn path() {
    let mut current_dir = std::env::current_dir().unwrap();
    println!("current_dir: {:?}", current_dir);

    println!("file_name: {:?}", current_dir.file_name());
    println!("pop: {:?}", current_dir.pop());
    println!("current_dir: {:?}", current_dir);
}

#[test]
fn empty_path_buf() {
    let empty_path_buf: PathBuf = PathBuf::new();
    println!("{:?}", empty_path_buf.to_str());
    check(empty_path_buf);

    let mut path_buf: PathBuf = PathBuf::new();
    path_buf.push("tmp");
    println!("{:?}", path_buf.to_str());
    check(path_buf);

    fn check(path_buf: PathBuf) {
        if path_buf.to_str().unwrap_or("") != "" {
            println!("not empty");
        } else {
            println!("emtpy");
        }
    }
}
