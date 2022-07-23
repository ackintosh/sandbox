// Tokioチュートリアル
// https://tokio.rs/tokio/tutorial/streams
// 日本語訳
// https://zenn.dev/magurotuna/books/tokio-tutorial-ja/viewer/streams

use tokio_stream::StreamExt;

#[tokio::test]
async fn basics() {
    // `Stream`とは「任意個のデータを非同期に扱うオブジェクト」で、言わば「非同期版Iterator」
    let mut stream = tokio_stream::iter(&[1, 2, 3]);

    // `Stream`には`next`メソッドが含まれて*8おり、 これを使うと「次のアイテムを取得する`Future`」を取得できる
    while let Some(v) = stream.next().await {
        println!("GOT = {:?}", v);
    }
}
