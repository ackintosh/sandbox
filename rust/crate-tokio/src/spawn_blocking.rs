// https://zenn.dev/tfutada/articles/5e87d6e7131e8e#3-2-spawn_bloking

// tokioには Worker threads と Blocking threads の2種類のスレッドがある

use std::time::Duration;

// シングルスレッドで実行する
#[tokio::test(flavor = "current_thread")]
async fn spawn_blocking() {
    // シングルスレッドで実行していて、かつメインスレッドが専有している(awaitしない)ので、
    // このタスクにスレッドが譲られず、実行されない
    tokio::spawn(async {
        tokio::time::sleep(Duration::from_secs(1)).await;
        println!("woke up 1"); // このタスクにスレッドが譲られないので出力されない
    });

    // `tokio::task::spawn_blocking` でタスクを作成しているので、Blocking threadsで動く
    let handle = tokio::task::spawn_blocking(move || {
        // async関数ではないので同期的に記述する
        std::thread::sleep(Duration::from_secs(1));
        println!("woke up 2");
    });

    std::thread::sleep(Duration::from_secs(3));
    println!("woke up 3");

    handle.await.unwrap();
}
