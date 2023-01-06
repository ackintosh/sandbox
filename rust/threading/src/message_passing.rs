// 参考
// https://zenn.dev/tfutada/articles/16766e3b4560db

use std::sync::{mpsc, Arc, Mutex};
use std::thread;
use std::time::Duration;

// /////////////////////////////////////////////////////////////////////////////////////////////////
// 単方向のみのメッセージパッシング
// /////////////////////////////////////////////////////////////////////////////////////////////////
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

// /////////////////////////////////////////////////////////////////////////////////////////////////
// senderチャネルが切断されるまでメッセージを受信しつづける
// /////////////////////////////////////////////////////////////////////////////////////////////////
mod read_until {
    use rand::Rng;

    // ///////////////////////////////
    // 単一のsender
    // ///////////////////////////////
    #[test]
    fn single_sender() {
        let (tx, rx) = std::sync::mpsc::channel();

        let join_handle = std::thread::spawn(move || {
            for i in 0..10 {
                tx.send(i).unwrap();
            }
        });

        loop {
            match rx.recv() {
                Ok(i) => println!("i: {}", i),
                Err(e) => {
                    // RecvErrorのドキュメントを参照
                    // > The recv operation can only fail if the sending half of
                    // > a [channel] (or [sync_channel]) is disconnected, implying that no further
                    // > messages will ever be received.
                    println!("senderチャネルが切断されました: {:?}", e);
                    // i: 0
                    // i: 1
                    // i: 2
                    // i: 3
                    // i: 4
                    // i: 5
                    // i: 6
                    // i: 7
                    // i: 8
                    // i: 9
                    // senderチャネルが切断されました: RecvError
                    break;
                }
            }
        }

        join_handle.join().unwrap();
    }

    // ///////////////////////////////
    // 複数のsender
    // ///////////////////////////////
    #[test]
    fn multiple_sender() {
        let (tx, rx) = std::sync::mpsc::channel();

        let mut handles = vec![];

        for _ in 0..2 {
            let tx_1 = tx.clone();
            handles.push(std::thread::spawn(move || {
                for i in 0..5 {
                    let mut rng = rand::thread_rng();
                    let uniform = rand::distributions::Uniform::new(1, 500);
                    std::thread::sleep(std::time::Duration::from_millis(rng.sample(uniform)));
                    tx_1.send(format!("{:?}: {}", std::thread::current().id(), i))
                        .unwrap();
                }
            }))
        }

        // メインスレッドが所有する sender チャネルは破棄しておく
        drop(tx);

        loop {
            match rx.recv() {
                Ok(message) => println!("{}", message),
                Err(e) => {
                    // RecvErrorのドキュメントを参照
                    // > The recv operation can only fail if the sending half of
                    // > a [channel] (or [sync_channel]) is disconnected, implying that no further
                    // > messages will ever be received.
                    println!("senderチャネルが 「すべて」切断されました: {:?}", e);
                    break;
                }
            }
        }

        for h in handles {
            let _ = h.join();
        }
    }
}

// /////////////////////////////////////////////////////////////////////////////////////////////////
// 単一の sender
// 複数の receiver
// https://zenn.dev/tfutada/articles/16766e3b4560db#%E5%8F%97%E4%BF%A1%E5%81%B4%E3%81%8C%E8%A4%87%E6%95%B0%E3%82%B9%E3%83%AC%E3%83%83%E3%83%89
// /////////////////////////////////////////////////////////////////////////////////////////////////
#[test]
fn single_sender_multiple_receiver() {
    let (tx, rx) = mpsc::channel();
    // 受信側のエンドポイントを排他制御する必要がある
    let shared_rx = Arc::new(Mutex::new(rx));

    for i in 1..5 {
        // 受信スレッドを生成する
        let rx = shared_rx.clone();
        thread::spawn(move || loop {
            // チャネルから受け取った値を保持する
            let mut n = 0;
            match rx.lock() {
                Ok(receiver) => {
                    n = receiver.recv().unwrap();
                }
                Err(e) => {
                    println!("error: {:?}", e);
                }
            }

            // ロックを取得しチャネルからrecvしないとココにはこない

            thread::sleep(Duration::from_secs(1)); // 重い演算処理の代わり

            println!("worker>{} {}", i, n);
        });
    }

    // 送信
    for i in 10..14 {
        tx.send(i).unwrap();
    }

    thread::sleep(Duration::from_secs(10));
}

// /////////////////////////////////////////////////////////////////////////////////////////////////
// メインスレッドと各スレッドの双方向のメッセージパッシング
// /////////////////////////////////////////////////////////////////////////////////////////////////
#[test]
fn multiplex() {
    let mut handles = vec![];
    let mut data = vec![1; 10];
    let mut sender_channels = vec![];
    let mut receiver_channels = vec![];

    for _ in 0..10 {
        // mainから各スレッドへのチャンネル
        let (send_tx, send_rx) = std::sync::mpsc::channel();
        // 各スレッドからmainへのチャンネル
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
