use std::cell::RefCell;

///////////////////////////////////////////////////////
// 標準ライブラリのスレッドローカル変数(thread local storage)
///////////////////////////////////////////////////////
thread_local! {

    // <RefCellで包んでいる理由>
    // * Rustは所有権と借用の仕組みによってデータ競合がおきないようになっている
    // * しかし、スレッドローカルのように、プログラムの任意の場所からアクセスできるデータについては、コンパイル時の検査(borrow check)ができない
    // * そこで、このborrow checkを実行時に行うデータ型のひとつ `RefCell` を使う
    // * ref: https://qiita.com/tatsuya6502/items/bed3702517b36afbdbca#%E3%83%9F%E3%83%A5%E3%83%BC%E3%82%BF%E3%83%96%E3%83%AB%E3%81%AA%E3%82%B9%E3%83%AC%E3%83%83%E3%83%89%E3%83%AD%E3%83%BC%E3%82%AB%E3%83%AB%E3%83%87%E3%83%BC%E3%82%BF%E3%82%92-thread_local-%E3%83%9E%E3%82%AF%E3%83%AD%E3%81%A8-refcell-%E3%81%A7%E5%AE%9F%E7%8F%BE%E3%81%99%E3%82%8B
    static RABBITS: RefCell<std::collections::HashSet<&'static str>> = {
        // 初帰化のコードはそのスレッドでRABBITSが初めてアクセスされたときに実行される
        // ここでは2つ要素を持つ HashSet を作成し、可変にするために RefCell で包んでいる
        let rb = ["ロップイヤー", "ダッチ"].iter().cloned().collect();
        RefCell::new(rb)
    }
}

#[test]
fn test() {
    // TLS(thread local storage)においた値にアクセスするには with を使う
    // メインスレッドのRABBITSが得られる
    RABBITS.with(|rb| {
        assert!(rb.borrow().contains("ロップイヤー"));

        // メインスレッドで要素を追加する
        rb.borrow_mut().insert("ネザーランド・ドワーフ");
    });

    // 別のスレッドを起動し、そこでも要素を追加する
    std::thread::spawn(|| {
        RABBITS.with(|rb| rb.borrow_mut().insert("ドワーフホト"))
    }).join().expect("thread error"); // スレッドの終了を待つ

    // メインスレッドのRABBITにアクセスする
    RABBITS.with(|rb| {
        assert!(rb.borrow().contains("ネザーランド・ドワーフ"));

        // RABBITSはスレッドごとに持つので、別スレッドで追加した要素はここにはない
        assert!(!rb.borrow().contains("ドワーフホト"));
    });
}
