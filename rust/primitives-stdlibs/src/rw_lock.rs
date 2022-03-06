// https://www.oreilly.co.jp/books/9784873119595/
// 3.8.3 RWロック

// https://doc.rust-jp.rs/the-rust-programming-language-ja/1.6/book/choosing-your-guarantees.html#mutext-%E3%81%A8-rwlockt

use std::sync::RwLock;

#[test]
fn test() {
    let lock = RwLock::new(10);

    {
        // immutableな参照を取得
        // スコープが外れたときに、自動的にReadロックが解放される
        let v1 = lock.read().unwrap();
        let v2 = lock.read().unwrap();
        println!("v1 = {}", v1);
        println!("v2 = {}", v2);
    }

    {
        // mutableな参照(正確には、RwLockWriteGuard型で包まれた参照)を取得
        let mut v = lock.write().unwrap();
        *v = 7;
        println!("v = {}", v);
    }
}
