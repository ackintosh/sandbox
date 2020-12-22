#[test]
fn usize_isize() {
    // std::mem::size_of()
    // https://doc.rust-lang.org/std/mem/fn.size_of.html
    // 型のサイズ(byte)を返す

    // https://doc.rust-jp.rs/book/second-edition/ch03-02-data-types.html#a%E6%95%B4%E6%95%B0%E5%9E%8B
    // usize, isizeのサイズは、64bitアーキテクチャの場合は 8 (8byte) を返す
    assert_eq!(
        8,
        std::mem::size_of::<usize>()
    );
    assert_eq!(
        8,
        std::mem::size_of::<isize>()
    );
}

#[test]
fn cmp() {
    let n = 10;
    let m = 20;

    match n.cmp(&m) {
        std::cmp::Ordering::Equal => println!("n = m"),
        std::cmp::Ordering::Greater => println!("n > m"),
        std::cmp::Ordering::Less => println!("n < m"),
    }

    // n < m が出力される
}
