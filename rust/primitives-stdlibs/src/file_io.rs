// 参考: https://qiita.com/fujitayy/items/12a80560a356607da637#%E6%96%87%E5%AD%97%E5%88%97%E3%83%90%E3%82%A4%E3%83%88%E5%88%97%E3%82%92%E4%B8%80%E5%BA%A6%E3%81%AB%E6%9B%B8%E3%81%8D%E5%87%BA%E3%81%99

use std::fs::File;
use std::io::{Read, Write};

// ファイルの内容全体をバイト列として一気に読み込み
#[test]
fn read() {
    let mut file = File::open("file_io/test_read.txt").unwrap();
    let mut buf = vec![];
    let size = file.read_to_end(&mut buf).unwrap();
    println!("size: {}, buf: {}", size, String::from_utf8(buf).unwrap());
}

// 文字列/バイト列を一度に書き出す
#[test]
fn write() {
    let mut file = File::create("file_io/test_write.txt").unwrap();
    file.write_all("test".as_bytes()).unwrap();
}
