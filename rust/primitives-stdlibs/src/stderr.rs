use std::io::Write;

#[test]
fn print() {
    eprintln!("error!");

    // Using implicit synchronization:
    std::io::stderr().write_all(b"error!!\n").unwrap();

    // Using explicit synchronization:
    {
        let stderr = std::io::stderr();
        let mut handle = stderr.lock();
        handle.write_all(b"error!!!\n").unwrap();
    }
}
