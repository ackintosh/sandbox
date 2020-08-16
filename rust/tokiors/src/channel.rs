#[test]
// #[tokio::main] // テストでは使えない
fn test() {
    let mut runtime = tokio::runtime::Runtime::new().unwrap();

    runtime.block_on(tokio_sync_mpsc_channel());
    runtime.block_on(tokio_sync_oneshot_channel());
}

////////////////////////////////////////////////////////////////////////////
// tokio::sync::mpsc::channel
////////////////////////////////////////////////////////////////////////////
async fn tokio_sync_mpsc_channel() {
    println!("/// tokio_sync_mpsc_channel ///");

    // * バッファに 5 を設定
    //   -> もしreceiverが受信せずにバッファが一杯になったら、sendはブロックされる
    // * senderは複製可能
    //   -> 複数のsenderから、単一のreceiverにメッセージを送信する
    let (mut sender, mut receiver) = tokio::sync::mpsc::channel(5);

    tokio::spawn(async move {
        for i in 0..10 {
            if let Err(e) = sender.send(i).await {
                // もしreceiverが閉じられていたらエラーが返る
                println!("[sender] the receiver dropped");
                println!("[sender] e: {:?}", e);
                return;
            }
        }
    });

    // senderが送信した順番にreceiverが受信する
    while let Some(i) = receiver.recv().await {
        println!("[receiver] got = {}", i)
    }

    println!("finished.");
}

////////////////////////////////////////////////////////////////////////////
// tokio::sync::oneshot::channel
////////////////////////////////////////////////////////////////////////////
async fn tokio_sync_oneshot_channel() {
    println!("/// tokio::sync::oneshot::channel ///");
    let (sender, receiver) = tokio::sync::oneshot::channel();

    tokio::spawn(async move {
        if let Err(_) = sender.send(3) {
            println!("[sender] the receiver dropped");
        }

        // 再度送信しようとしても sender が move されているのでコンパイルエラーになる
        // sender.send(5);

        // error[E0382]: use of moved value: `sender`
        //   --> tokiors/src/channel.rs:53:9
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
