// https://github.com/clap-rs/clap

// demo
// https://github.com/clap-rs/clap/blob/v3.1.8/examples/derive_ref/README.md#overview

use clap::Parser;

// https://github.com/clap-rs/clap#example
#[derive(Parser, Debug)]
struct CliArgs {
    #[clap(short, long)] // short で `-n`、long で `--name` オプションが使えるようになる
    name: String,
    #[clap(short, long)] // short で `-c`、long で `--count` オプションが使えるようになる
    count: u8,
    #[clap(flatten)]
    env: Env,
}

// 環境変数を構造体にマッピングする
// https://github.com/clap-rs/clap/blob/v3.1.8/examples/derive_ref/README.md#arg-attributes
#[derive(Parser, Debug)]
struct Env {
    #[clap(env)]
    test_name: String,
    #[clap(env)]
    test_count: u8,
}

// 実行例
// `$ TEST_NAME=env_name TEST_COUNT=100 cargo run -- --name foo --count 2`
fn main() {
    let cli_args: CliArgs = CliArgs::parse();

    println!("{:?}", cli_args);
    for _ in 0..cli_args.count {
        println!("Hello {}!", cli_args.name);
    }
}
