use std::env::VarError;

// clapでも環境変数を構造体にマッピングできるのでそちらが便利

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
}
