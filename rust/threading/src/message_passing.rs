// 単方向のみのメッセージパッシング
#[test]
fn simplex() {
    let (tx, rx) = std::sync::mpsc::channel();
    let handle = std::thread::spawn(move || {
        let data = rx.recv().unwrap();
        println!("receiver: {}", data);
    });

    let _ = tx.send("Hello, world!");

    let _ = handle.join();
}

// メインスレッドと各スレッドの双方向のメッセージパッシング
#[test]
fn multiplex() {
    let mut handles = vec![];
    let mut data = vec![1; 10];
    let mut sender_channels = vec![];
    let mut receiver_channels = vec![];

    for _ in 0..10 {
        let (send_tx, send_rx) = std::sync::mpsc::channel();
        let (receive_tx, receive_rx) = std::sync::mpsc::channel();

        sender_channels.push(send_tx);
        receiver_channels.push(receive_rx);

        handles.push(std::thread::spawn(move || {
            let mut data = send_rx.recv().unwrap();
            data += 1;
            let _ = receive_tx.send(data);
        }));
    }

    // 各スレッドにdataを送信
    for i in 0..10 {
        // この例では問題ないが、
        // スレッド間を安全に渡すことが出来ない型をチャンネルを通して送ろうとするとコンパイルエラーになる
        let _ = sender_channels[i].send(i);
    }

    // 各スレッドからの結果をdataに格納
    for i in 0..10 {
        data[i] = receiver_channels[i].recv().unwrap();
    }

    for h in handles {
        let _ = h.join();
    }

    dbg!(data);
}
