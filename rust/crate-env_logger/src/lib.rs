// logクレートのマクロのログレベルを環境変数経由で設定できる
#[macro_use]
extern crate log;

#[test]
fn it_works() {
    // 別のテストで、init() を実行しているので
    // こちらは try_init() にする
    let _ = env_logger::try_init();

    debug!("debugログ: {}", "xxxxx");
    error!("errorログ: {}", "xxxxx");

    // $ RUST_LOG=error cargo test
    // で実行すると error ログだけが表示される
    // [2020-07-13T09:11:51Z ERROR crate-env_logger] errorログ: xxxxx
}

mod builder {
    use env_logger::{Builder, Env};

    #[test]
    fn default() {
        // デフォルトの環境変数 `RUST_LOG` から設定値を取る
        let mut builder = Builder::from_env(Env::default());
        // 別のテストで、env_logger::init() を実行しているので
        // こちらは try_init() にする
        let _ = builder.try_init();

        debug!("builder: {}", "test");
    }

    #[test]
    fn custom_env() {
        // 環境変数 `CUSTOM_ENV` から設定値を取る
        let mut builder = Builder::from_env(Env::new().filter("CUSTOM_ENV"));
        // 別のテストで、env_logger::init() を実行しているので
        // こちらは try_init() にする
        let _ = builder.try_init();

        debug!("custom_env: {}", "test");

        // $ CUSTOM_ENV=debug cargo test builder::custom_env
        // で実行すると環境変数が反映される
    }
}
