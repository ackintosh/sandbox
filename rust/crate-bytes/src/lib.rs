use bytes::{BufMut, Bytes, BytesMut};

// *** Bytesを使うモチベーション ***
// * データを渡す際、シンプルにバイトデータ(&[u8]やVecなど)をあちらこちらに渡しながらメモリプールを使用することも良いのですが、
//   極端な話、受信したデータが大きい場合(1GBとか)、それをVec<[u8]>にすると大量のメモリを占領してしまうハメになります(本当に極端な例です)。
//   Bytesは、複数のBytesオブジェクトが同じ基本メモリを指すようにすることで、ゼロコピーのプログラミングを促進します。
//   これは、参照カウント(Reference Counter)を使用し、メモリが不要になり、解放できるようになったときに追跡することで管理されます。
//
// * tokioでTCPサーバを実装する際、channelを利用してやりとりをするケースがよくあります。
//   その場合、1:Nで同じデータを送信することが多いですが、Bytesを使うと、例えば1万個のchannelにデータを送ってもBytesを維持するための小さなスペースを除いては、
//   実際にコピーされるデータはありません(データは全部同じメモリを参照している)

#[test]
fn bytes_mut() {
    // * BytesMutはbufferを書き込むためのmemory buffer実装
    // * 一般的にbytesMut::with_capacity(1024)のような感じで初期化しますが、メモリ不足時は自動的にメモリを確保します
    // * BytesMutの特徴としては、Deep CopyではなくShallown CopyベースのポインタとReference Counterで実装されているためメモリを効率よく使います
    let mut buf = BytesMut::with_capacity(1024);
    buf.put(&b"hello, world"[..]);

    assert_eq!(12, buf.len());
}

#[test]
fn bytes() {
    // Bytesは読み取り専用のmemory buffer実装
    let mut mem = Bytes::from("hello world");
    let a = mem.slice(0..5);

    assert_eq!(a, "hello");

    let b = mem.split_to(6);

    assert_eq!(mem, "world");
    assert_eq!(b, "hello ");
}
