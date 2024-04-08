// https://github.com/tokio-rs/tracing?tab=readme-ov-file#in-asynchronous-code

// * 非同期関数のスパンには tracing::instrument マクロか、もしくは tracing::Instrument トレイトを使用する必要があります
// * Span::enterなどでスパンに一度入った際、awaitを跨いでenter用のガードを持たせると正しくないトレースを吐くことがあるよう
//     https://docs.rs/tracing/latest/tracing/index.html#spans
//    * tracing::Instrumentトレイトを使う場合は、これをuseしておくと、たとえばFutureにinstrumentというメソッドが生えてくる
