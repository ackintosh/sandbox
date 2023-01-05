// https://zenn.dev/tfutada/articles/5e87d6e7131e8e#3-3-join!

use std::time::Duration;

#[tokio::test]
async fn join() {
    // 注意:
    //   * 2つの async ブロックは(例えマルチスレッドであっても)同一のOSスレッドで処理される
    //   * `tokio::spawn` で async ブロックを実行することで、マルチスレッド上でパラレルに実行できる
    //         let handle1 = tokio::spawn(async { ....

    let logic1 = async {
        println!("logic1...");
        std::thread::sleep(Duration::from_secs(3));
    };

    let logic2 = async {
        println!("logic2... will start one logic1 is done.");
        std::thread::sleep(Duration::from_secs(3));
    };

    println!("waiting at join!");
    // asyncブロックはすぐには実行されず、 `join!` で開始する
    // なので、"waiting at join!" のあとに "logic1..." が出力される
    tokio::join!(logic1, logic2);

    println!("all done");
}
