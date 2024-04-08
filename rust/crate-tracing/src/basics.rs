// 実行方法
// ```shell
// $ RUST_LOG=info cargo test
// ```
#[test]
fn test() {
    // 別のテストで init 済みの可能性があるので try_init のResultは捨てている
    let _ = tracing_subscriber::fmt::try_init();

    tracing::info!("Hello, tracing!");
    tracing::error!("Hello, tracing!");
    tracing::error!("crate-tracing. v{}", env!("CARGO_PKG_VERSION"));
}

// ref https://github.com/tokio-rs/tracing#usage
//
// 実行方法
// cargo test official_usage::yak_shave
mod official_usage {
    #[test]
    fn yak_shave() {
        // 別のテストで init 済みの可能性があるので try_init のResultは捨てている
        let _ = tracing_subscriber::fmt::try_init();

        let number_of_yaks = 3;
        // this creates a new event, outside of any spans.
        tracing::error!(number_of_yaks, "preparing to shave yaks.");

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

// `#[tracing::instrument]`
// ref https://github.com/tokio-rs/tracing?tab=readme-ov-file#in-libraries
//
// 実行方法
// cargo test instrument::instrument
//    -> `#[tracing::instrument]` を追加したメソッドで、ログに、メソッド呼び出し時の引数が一緒に出力される
mod instrument {
    #[test]
    fn instrument() {
        // 別のテストで init 済みの可能性があるので try_init のResultは捨てている
        let _ = tracing_subscriber::fmt::try_init();

        instrument_inner("arg for inner".into());
    }

    #[tracing::instrument]
    fn instrument_inner(arg: String) {
        tracing::error!("inner");
        tracing::error!("{}", &arg);

        instrument_inner_inner("arg for inner inner".into())
    }

    #[tracing::instrument]
    fn instrument_inner_inner(arg: String) {
        tracing::error!("inner inner");
        tracing::error!("{}", &arg);
    }
}

// span
// ref https://github.com/tokio-rs/tracing?tab=readme-ov-file#in-libraries
//
// 実行方法
// RUST_LOG=trace cargo test basics::span
//   -> spanを TRACE レベルで作成しているので、spanの効果を確認するにはRUST_LOG=traceにする
//   -> spanのスコープ内で出力するログに、span名とyaks変数の中身がログに出る
mod span {
    #[test]
    fn test() {
        // 別のテストで init 済みの可能性があるので try_init のResultは捨てている
        let _ = tracing_subscriber::fmt::try_init();

        let yaks_shaved = shave_all(10);
        tracing::info!(yaks_shaved);
    }

    fn shave_all(yaks: usize) -> usize {
        // Constructs a new span named "shaving_yaks" at the TRACE level,
        // and a field whose key is "yaks". This is equivalent to writing:
        //
        // let span = span!(Level::TRACE, "shaving_yaks", yaks = yaks);
        //
        // local variables (`yaks`) can be used as field values
        // without an assignment, similar to struct initializers.
        let span = tracing::span!(tracing::Level::TRACE, "shaving_yaks", yaks);
        let _enter = span.enter();

        tracing::info!("starting shave_all");

        let mut yaks_shaved = 0;
        for yak in 1..=yaks {
            let res = shave(yak);
            tracing::debug!(yak, shaved = res.is_ok());

            if let Err(ref error) = res {
                // Like spans, events can also use the field initialization shorthand.
                // In this instance, `yak` is the field being initialized.
                tracing::error!(yak, error = error.as_ref(), "failed to shave yak!");
            } else {
                yaks_shaved += 1;
            }
            tracing::debug!(yaks_shaved);
        }

        yaks_shaved
    }

    #[tracing::instrument]
    fn shave(yak: usize) -> Result<(), Box<dyn std::error::Error + 'static>> {
        // this creates an event at the DEBUG level with two fields:
        // - `excitement`, with the key "excitement" and the value "yay!"
        // - `message`, with the key "message" and the value "hello! I'm gonna shave a yak."
        //
        // unlike other fields, `message`'s shorthand initialization is just the string itself.
        tracing::debug!(excitement = "yay!", "hello! I'm gonna shave a yak.");

        if yak == 3 {
            tracing::warn!("could not locate yak!");
            // note that this is intended to demonstrate `tracing`'s features, not idiomatic
            // error handling! in a library or application, you should consider returning
            // a dedicated `YakError`. libraries like snafu or thiserror make this easy.
            return Err(
                std::io::Error::new(std::io::ErrorKind::Other, "shaving yak failed!").into(),
            );
        } else {
            tracing::debug!("yak shaved successfully");
        }

        Ok(())
    }
}
