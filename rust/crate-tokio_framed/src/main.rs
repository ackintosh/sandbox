// Rust: tokioを使って独自プロトコルのメッセージを受け取るTCPサーバーを作る - castaneaiのブログ
// https://castaneai.hatenablog.com/entry/rust-tcp-server-with-custom-protocol

use tokio::net::TcpListener;
use tokio_stream::StreamExt;
use tokio_util::codec::{FramedRead, LengthDelimitedCodec};

// /////////////////////////////////////
// サーバに3byteのデータを送信する
//
// $ python3
// >>> import socket
// >>> s = socket.socket()
// >>> s.connect(("127.0.0.1", 12345))
// >>> s.send(b"\x00\x00\x00\x03abc")
// 7
// /////////////////////////////////////

#[tokio::main]
async fn main() {
    let listener = TcpListener::bind("127.0.0.1:12345").await.unwrap();
    loop {
        let (client, _) = listener.accept().await.unwrap();
        let mut frame_reader = FramedRead::new(client, LengthDelimitedCodec::new());
        while let Some(frame) = frame_reader.next().await {
            match frame {
                Ok(data) => println!("received: {:?}", data),
                Err(err) => eprintln!("error: {:?}", err),
            }
        }
    }
}
