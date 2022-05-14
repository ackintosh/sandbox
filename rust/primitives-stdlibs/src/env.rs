// clapでも環境変数を構造体にマッピングできるのでそちらが便利

// Cargo組み込みの環境変数
// Environment Variables - The Cargo Book
// https://doc.rust-lang.org/cargo/reference/environment-variables.html

use std::path::PathBuf;

#[test]
fn env() {
    let foo = match std::env::var("FOO") {
        Ok(v) => v,
        Err(err) => {
            println!("err: {}", err);
            "".to_string()
        }
    };
    println!("{foo}");

    // 参考
    // https://github.com/sigp/lighthouse/blob/6d4af4c9cac2b8d3aed94bd75305f9f9a5d6a326/common/eth2_config/src/lib.rs#L79
    let path = std::env::var("PATH").expect("should have $PATH environment variable");
    println!("{path}");

    for (key, value) in std::env::vars() {
        println!("key: {}, value: {}", key, value);
    }

    if let Ok(_) =
        std::env::var("RUST_LOG").and_then(|log_level| Ok(log_level == "debug".to_owned()))
    {
        println!("debug!!!");
    }

    // /////////////
    // env! マクロ
    // /////////////
    // 例: Cargo.toml のバージョンを出力する
    println!("CARGO_PKG_VERSION: {}", env!("CARGO_PKG_VERSION"));
    // 存在しない環境変数を参照している場合、実行時にエラーになる
    // error: environment variable `XXXXX` not defined
    // println!("XXXXX: {}", env!("XXXXX"));

    // そのパッケージの Cargo.toml が存在するディレクトリ
    println!("CARGO_MANIFEST_DIR: {}", env!("CARGO_MANIFEST_DIR"));
    // 例:
    // let path_buf = env!("CARGO_MANIFEST_DIR")
    //     .parse::<PathBuf>()
    //     .expect("should parse manifest dir as path")
    //     .join("foo");
}
