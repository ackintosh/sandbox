// clapでも環境変数を構造体にマッピングできるのでそちらが便利

// Cargo組み込みの環境変数
// Environment Variables - The Cargo Book
// https://doc.rust-lang.org/cargo/reference/environment-variables.html

// 環境変数を取得する
#[test]
fn get_env() {
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

    // //////////////////////////////////////////////////////////
    // env! マクロ
    // //////////////////////////////////////////////////////////
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

    // 実行時(runtime)にセットする環境変数は、 env! では取れない
    //   -> env! は compile time に環境変数を解決するので。
    //      runtimeに環境変数を取得したい場合は std::env::var() を使う
    std::env::set_var("A_TEST_ENV_VAR", "VALUE");
    // env!("A_TEST_ENV_VAR");
    //
    // error: environment variable `A_TEST_ENV_VAR` not defined
    //   --> primitives-stdlibs/src/env.rs:58:5
    //    |
    // 58 |     env!("A_TEST_ENV_VAR");
    //    |     ^^^^^^^^^^^^^^^^^^^^^^
    //    |
    //    = note: this error originates in the macro `env` (in Nightly builds, run with -Z macro-backtrace for more info)
}

// 環境変数を設定する
#[test]
fn set_env() {
    std::env::set_var("A_TEST_ENV_VAR", "VALUE");

    println!("{:?}", std::env::var("A_TEST_ENV_VAR"));
}
