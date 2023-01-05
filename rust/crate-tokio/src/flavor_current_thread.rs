// https://zenn.dev/tfutada/articles/5e87d6e7131e8e#2-2-%E3%82%B7%E3%83%B3%E3%82%B0%E3%83%AB%E3%82%B9%E3%83%AC%E3%83%83%E3%83%89%E3%81%AB%E3%81%97%E3%81%A6%E3%81%BF%E3%82%88%E3%81%86

use std::time::Duration;

// `#[tokio::main(flavor = "current_thread")]` と指定すると、Node.jsのようにOSスレッドが１つだけのランタイムになる
//
// シングルスレッド(flavor = "current_thread")で実行していて、
// かつ、メインのタスクで同期スリープ(std::thread::sleep())を使っているので、
// `tokio::spawn()` で生成したタスクにスレッドが譲られることなくプログラムが終了してしまう.
#[tokio::test(flavor = "current_thread")]
async fn current_thread() {
    // ここで生成したタスクにスレッドが譲られることなくプログラムが終了してしまう
    tokio::spawn(async {
        tokio::time::sleep(Duration::from_secs(3)).await;
        println!("woke up!");
    });

    // 注意: `std` の sleep を使っている -> 同期スリープである
    std::thread::sleep(Duration::from_secs(3));
    // 非同期版の sleep を使い、`await` を入れることで別のタスクにスレッドが譲られる
    //   -> プログラマが協調的(cooperative)にタスクをスケジューリングする必要がある
    // tokio::time::sleep(Duration::from_secs(5)).await;
    println!("Done");
}
