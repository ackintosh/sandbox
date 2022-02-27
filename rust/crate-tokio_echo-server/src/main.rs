// 並行プログラミング入門 https://www.oreilly.co.jp/books/9784873119595/
// 5.4 非同期ライブラリ

// /////////////////////////////////
// [Tokio を用いた echo サーバの実装例]
// * これと同等なコードは通常のスレッドを用いても記述できるが、実行時コストで非同期ライブラリのメリットがある
//   * 通常、スレッドの生成はコストの高い操作のため、単位時間あたりのコネクション到着数が増加した時、計算リソースが不足してしまう
//   * Tokio など非同期ライブラリの場合、コネクション到着ごとにスレッドを生成するのではなく、あらかじめスレッドを生成しておき、そのスレッドで各タスクを実行する
// /////////////////////////////////

use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

#[tokio::main] // 非同期用の main 関数にはこれを指定する
async fn main() -> tokio::io::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:10000").await.unwrap();

    loop {
        // TCPコネクションをアクセプトする
        let (mut socket, addr) = listener.accept().await?;
        println!("accept: {}", addr);

        // 非同期タスクを作成する
        tokio::spawn(async move {
            // バッファ読み書き用オブジェクト生成
            let (r, w) = socket.split();
            let mut reader = tokio::io::BufReader::new(r);
            let mut writer = tokio::io::BufWriter::new(w);

            let mut line = String::new();

            loop {
                line.clear(); // 前回のループで追記された文字列をクリアしておく

                match reader.read_line(&mut line).await {
                    Ok(0) => {
                        // コネクションクローズ
                        println!("closed: {}", addr);
                        return;
                    }
                    Ok(_) => {
                        print!("read: {}, {}", addr, line);
                        writer.write_all(line.as_bytes()).await.unwrap();
                        writer.flush().await.unwrap();
                    }
                    Err(e) => {
                        // エラー
                        println!("error: {}, {}", addr, e);
                        return;
                    }
                }
            }
        });
    }
}
