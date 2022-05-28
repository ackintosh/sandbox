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
    tracing::error!("Hello, tracing!");
}

// https://github.com/tokio-rs/tracing#usage
mod official_usage {
    #[test]
    fn yak_shave() {
        let _ = tracing_subscriber::fmt::try_init();

        let number_of_yaks = 3;
        // this creates a new event, outside of any spans.
        tracing::error!(number_of_yaks, "preparing to shave yaks");

        let number_shaved = shave_all(number_of_yaks);
        tracing::error!(
            all_yaks_shaved = number_shaved == number_of_yaks,
            "yak shaving completed."
        );
    }

    fn shave_all(n: i32) -> i32 {
        n
    }
}

mod instrument {
    #[test]
    #[tracing::instrument()]
    fn instrument() {
        let _ = tracing_subscriber::fmt::try_init();
        instrument_inner("arg for inner".into());
    }

    #[tracing::instrument()]
    fn instrument_inner(arg: String) {
        tracing::error!("inner");
        tracing::error!("{}", &arg);

        instrument_inner_inner("arg for inner inner".into())
    }

    #[tracing::instrument()]
    fn instrument_inner_inner(arg: String) {
        tracing::error!("inner inner");
        tracing::error!("{}", &arg);
    }
}
