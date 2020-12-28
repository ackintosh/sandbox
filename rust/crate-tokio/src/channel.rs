use chrono::prelude::*;
use futures::core_reexport::time::Duration;

#[test]
// #[tokio::main] // テストでは使えない
fn test() {
    let mut runtime = tokio::runtime::Runtime::new().unwrap();

    runtime.block_on(tokio_sync_mpsc_channel());
    runtime.block_on(tokio_sync_oneshot_channel());
}

////////////////////////////////////////////////////////////////////////////
// tokio::sync::mpsc::channel
// mpsc -> multi-producer, single-consumerの略
////////////////////////////////////////////////////////////////////////////
async fn tokio_sync_mpsc_channel() {
    println!("////////////////////////////////////////////////");
    println!("/// tokio_sync_mpsc_channel ///");
    println!("////////////////////////////////////////////////");
    println!("/// {} ///", Local::now());
    println!("/// {:?} ///", std::thread::current().id());

    // * バッファに 5 を設定
    //   -> もしreceiverが受信せずにバッファが一杯になったら、sendはブロックされる
    // * senderは複製可能
    //   -> 複数のsenderから、単一のreceiverにメッセージを送信する
    let (mut sender, mut receiver) = tokio::sync::mpsc::channel(5);

    tokio::spawn(async move {

        // テストでsleepを入れている
        tokio::time::delay_for(Duration::from_secs(10)).await;

        for i in 0..10 {
            if let Err(e) = sender.send(i).await {
                // もしreceiverが閉じられていたらエラーが返る
                println!("[sender] the receiver dropped");
                println!("[sender] e: {:?}", e);
                return;
            }
            println!("{} [sender] sent a message. {:?}", Local::now(), std::thread::current().id());
        }
    });

    println!("{} [receiver] ready to receive values from a sender. {:?}", Local::now(), std::thread::current().id());
    // senderが送信した順番にreceiverが受信する
    while let Some(i) = receiver.recv().await {
        println!("{} [receiver] got = {}. {:?}", Local::now(), i, std::thread::current().id());
    }

    println!("{} finished. {:?}", Local::now(), std::thread::current().id());
}

////////////////////////////////////////////////////////////////////////////
// tokio::sync::oneshot::channel
////////////////////////////////////////////////////////////////////////////
async fn tokio_sync_oneshot_channel() {
    println!("////////////////////////////////////////////////");
    println!("/// tokio::sync::oneshot::channel ///");
    println!("////////////////////////////////////////////////");
    let (sender, receiver) = tokio::sync::oneshot::channel();

    tokio::spawn(async move {
        if let Err(_) = sender.send(3) {
            println!("[sender] the receiver dropped");
        }

        // 再度送信しようとしても sender が move されているのでコンパイルエラーになる
        // sender.send(5);

        // error[E0382]: use of moved value: `sender`
        //   --> crate-tokio/src/channel.rs:53:9
        //    |
        // 49 |         if let Err(_) = sender.send(3) {
        //    |                         ------ value moved here
        // ...
        // 53 |         sender.send(5);
        //    |         ^^^^^^ value used here after move
        //    |
        //    = note: move occurs because `sender` has type `tokio::sync::oneshot::Sender<i32>`, which does not implement the `Copy` trait
    });

    match receiver.await {
        Ok(v) => println!("[receiver] got = {:?}", v),
        Err(_) => println!("[receiver] the sender dropped"),
    }
}
