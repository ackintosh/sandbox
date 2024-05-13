// https://github.com/dtolnay/anyhow

// 参考
// * 2023-08-12 Rustのエラーハンドリングを楽にするanyhowの使い方 - テックブログです https://ai-techblog.hatenablog.com/entry/rust-anyhow-usage
// * 2021-12-01 Rust/AnyhowのTips https://zenn.dev/yukinarit/articles/b39cd42820f29e

#[cfg(test)]
mod tests {

    // * context はエラーにコンテキスト情報を付与
    // * with_context はエラー発生時のみ遅延評価されコンテキスト情報を付与

    use anyhow::Context; // Result型に `with_context()` や `context()` が生える
    use std::path::PathBuf;

    // `with_context()` でエラー時にコンテキスト情報を付与する
    //   -> `format!` でエラー文を作ったりする場合だと `context()` だと毎回format!が呼ばれてしまうので、`with_context()` でクロージャを渡すようにすると良い
    #[test]
    fn with_context() {
        // 関数の返り値の型を `anyhow::Result` にすることで、
        //   * `E` を省略できる
        //   * `anyhow::Error` は `Box<dyn std::error::Error>` のように振る舞うので、`?` を使ったearly returnで見通しの良いコードが書ける
        let read_file = |path: PathBuf| -> anyhow::Result<Vec<u8>> {
            // `use anyhow::Context` することでResult型に `with_context()` や `context()` が生える
            let content = std::fs::read(&path).with_context(|| {
                format!("Failed to read the path: {}", path.display())
            })?;

            Ok(content)
        };

        let result = read_file(PathBuf::from("xxx.txt"));

        // * with_contextで付加したコンテキスト情報が出力される
        // * `{:?}` で文字列出力しているので、backtraceが出力される
        println!("result: {:?}", result);
        // Err(Failed to ready the path: xxx.txt
        //
        // Caused by:
        //     No such file or directory (os error 2)
        //
        // Stack backtrace:
        //    0: std::backtrace_rs::backtrace::libunwind::trace
        // ...
        // ...
    }

    #[test]
    fn anyhow_macro() {
        let validate = |str: &str| -> anyhow::Result<()> {
            if str.len() != 16 {
                // anyhow! マクロを使うことで `anyhow::Result` 型を簡単に作れる
                return Err(anyhow::anyhow!("str length must be 16 characters, got {}", str))
            };

            Ok(())
        };

        let result = validate("1234567890");
        println!("[anyhow] result: {:?}", result);
    }

    #[test]
    fn bail_macro() {
        let validate = |str: &str| -> anyhow::Result<()> {
            if str.len() != 16 {
                // bail! マクロを使うことで `return Err(anyhow!(...)` と書く必要がなくなる
                anyhow::bail!("str length must be 16 characters, got {}", str);
            };

            Ok(())
        };

        let result = validate("1234567890");
        println!("[bail] result: {:?}", result);
    }
}
