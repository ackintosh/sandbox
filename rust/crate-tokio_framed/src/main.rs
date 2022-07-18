// Rust: tokioを使って独自プロトコルのメッセージを受け取るTCPサーバーを作る - castaneaiのブログ
// https://castaneai.hatenablog.com/entry/rust-tcp-server-with-custom-protocol

use std::io::Error;
use bytes::{Bytes, BytesMut};
use tokio::net::TcpListener;
use tokio_stream::StreamExt;
use tokio_util::codec::{Framed, FramedRead, LengthDelimitedCodec};
use futures::sink::SinkExt;

// /////////////////////////////////////
// サーバに3byteのデータを送信する
//
// * 送信するデータ
//   先頭4バイトに長さが (3) あり、その後にその長さ分のデータ (abc) が入っている
//   +---- len: u32 ----+---- data ----+
//   | \x00\x00\x00\x03 |  abc       |
//   +------------------+--------------+
// /////////////////////////////////////
#[tokio::main]
async fn main() {
    // read_only().await;
    echo().await;
}

// *** 受信するだけ ***
//
// *** クライアント側のコマンド ***
// $ python3
// >>> import socket
// >>> s = socket.socket()
// >>> s.connect(("127.0.0.1", 12345))
// >>> s.send(b"\x00\x00\x00\x03abc")
// 7 (送信したバイト数)
async fn read_only() {
    let listener = TcpListener::bind("127.0.0.1:12345").await.unwrap();

    loop {
        let (client, _) = listener.accept().await.unwrap();

        // デフォルトの LengthDelimitedCodec では
        // 先頭4バイトにデータの長さが格納される設定になっている
        let mut frame_reader = FramedRead::new(client, LengthDelimitedCodec::new());

        while let Some(frame) = frame_reader.next().await {
            match frame {
                Ok(data) => println!("received: {:?}", data),
                Err(err) => eprintln!("error: {:?}", err),
            }
        }
    }
}

// *** エコーサーバ ***
// 受信したデータを、`SinkExt::send()` を利用して返している
//
// *** クライアント側のコマンド ***
// $ python3
// >>> import socket
// >>> s = socket.socket()
// >>> s.connect(("127.0.0.1", 12345))
// >>> s.send(b"\x00\x00\x00\x03abc")
// 7 (送信したバイト数)
// >>> s.recv(1024)
// b'\x00\x00\x00\x03abc' (エコーサーバが返したレスポンス)
async fn echo() {
    let listener = TcpListener::bind("127.0.0.1:12345").await.unwrap();

    loop {
        let (client, _) = listener.accept().await.unwrap();

        let mut framed = Framed::new(client, LengthDelimitedCodec::new());

        while let Some(frame) = framed.next().await {
            match frame {
                Ok(data) => {
                    framed.send(Bytes::from(data)).await.unwrap();
                }
                Err(err) => eprintln!("error: {:?}", err),
            }
        }
    }
}
