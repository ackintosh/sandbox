use std::env;
use std::error::Error;
use std::io::{Read, Write};
use std::net::TcpListener;

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = env::args().collect();
    let addr = &args[1];
    echo_server(addr)?;

    Ok(())
}

fn echo_server(address: &str) -> Result<(), Box<dyn Error>> {
    let listener = TcpListener::bind(address)?;

    loop {
        // スレッドをブロックし、クライアントからのコネクション確立要求を待機する
        // TCPのスリーウェイハンドシェイクを通してコネクションが確立されたらブロックを解除する
        let (mut stream, _) = listener.accept()?;

        // スレッドを立ち上げて接続に対応する
        std::thread::spawn(move || {
            let mut buffer = [0u8; 1024];

            loop {
                // スレッドをブロックし、データの受信を待機する
                let nbytes = stream.read(&mut buffer).unwrap();
                if nbytes == 0 {
                    return;
                }
                println!("{}", String::from_utf8_lossy(&buffer[..nbytes]));
                // クライアントにデータを送信する
                stream.write_all(&buffer[..nbytes]).unwrap();
            }
        });
    }
}
