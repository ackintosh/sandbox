// https://github.com/tokio-rs/tracing

// Rust: Into tracing world - Qiita
// https://qiita.com/gemhung/items/bd4c4617b58250689f47

// ```shell
// $ RUST_LOG=info cargo test
// ```
#[test]
fn test() {
    let _ = tracing_subscriber::fmt::try_init();
    tracing::info!("Hello, tracing!");
}

#[test]
#[tracing::instrument()]
fn instrument() {
    let _ = tracing_subscriber::fmt::try_init();
    instrument_inner("arg for inner".into());
}

#[tracing::instrument()]
fn instrument_inner(arg: String) {
    tracing::info!("inner");
    tracing::info!("{}", &arg);

    instrument_inner_inner("arg for inner inner".into())
}

#[tracing::instrument()]
fn instrument_inner_inner(arg: String) {
    tracing::info!("inner inner");
    tracing::info!("{}", &arg);
}
