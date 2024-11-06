use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use reqwest::Identity;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let res = reqwest::get("https://httpbin.org/ip")
        .await?
        .json::<HashMap<String, String>>()
        .await?;

    println!("{:#?}", res);
    // {
    //     "origin": "116.91.233.176",
    // }

    Ok(())
}

// cd crate-reqwest
// openssl req -x509 -sha256 -nodes -days 36500 -newkey rsa:4096 -keyout key.key -out cert.pem -config openssl_config
// openssl pkcs12 -export -aes256 -out key.p12 -inkey key.key -in cert.pem -password pass:bark
//
// # 1. 秘密鍵の生成
// openssl genrsa -out server.key 2048
// # 2. CSRの作成
// openssl req -new -key server.key -out server.csr
// # 3. 自己署名証明書の作成
// openssl x509 -req -days 365 -in server.csr -signkey server.key -out server.crt
// # 4. PKCS#12ファイルの作成
// openssl pkcs12 -export -out server.p12 -inkey server.key -in server.crt -password pass:bark
#[test]
fn test_identity_from_pkcs12_der() {
    let path = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("server.p12");
    let mut buf = Vec::new();
    File::open(path)
        .unwrap()
        .read_to_end(&mut buf)
        .unwrap();
    let password = "bark";
    let r = Identity::from_pkcs12_der(&buf, password);
    println!("{r:?}");
}

