use std::cell::RefCell;

///////////////////////////////////////////////////////
// 標準ライブラリのスレッドローカル変数(thread local storage)
///////////////////////////////////////////////////////
thread_local! {
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
