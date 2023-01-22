// 参考
// https://gist.github.com/meganehouser/a5ec875b454b83dfaf1ae83bceb1c34b

// 後述の BufWriter を使ったほうがよい
// std::fs::File の write, read はバッファリングされないため
mod stdfs {
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

    #[test]
    fn append() {
        let mut file = File::options()
            .create(true)
            .append(true)
            .open("file_io/stdfs_append.txt")
            .unwrap();
        file.write_all("test".as_bytes()).unwrap();
        file.write_all("test".as_bytes()).unwrap();
    }
}

// RustのファイルIOには BufReader, BufWriter を使う. バッファリングを利用するため.
mod bufwriter {
    use std::io::{BufWriter, Write};

    #[test]
    fn buf_writer() {
        let mut dest = std::env::current_dir().unwrap();
        dest.push("file_io");
        dest.push("buf_writer.log");
        println!("{:?}", dest);

        let mut writer = BufWriter::new(std::fs::File::create(dest).unwrap());
        let b = b"test";
        for _ in 0..10 {
            writer.write(b).unwrap();
        }
    }
}
