#[cfg(test)]
mod tests {
    use std::env;
    use std::fs::File;
    use std::io::Read;
    use std::path::PathBuf;
    use security_framework::import_export::Pkcs12ImportOptions;

    // # 1. 秘密鍵の生成
    // openssl genrsa -out server.key 2048
    // # 2. CSRの作成
    // openssl req -new -key server.key -out server.csr
    // # 3. 自己署名証明書の作成
    // openssl x509 -req -days 365 -in server.csr -signkey server.key -out server.crt
    // # 4. PKCS#12ファイルの作成
    // openssl pkcs12 -export -out server.p12 -inkey server.key -in server.crt -password pass:bark
    // # 4-2. PKCS#12ファイルの作成 (-legacyオプション)
    // # -legacyオプションの必要性 https://github.com/kornelski/rust-security-framework/issues/216#issuecomment-2466496614
    // openssl pkcs12 -legacy -export -out server_legacy.p12 -inkey server.key -in server.crt -password pass:bark
    //
    #[test]
    fn test() {
        // let path = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("server.p12");
        let path = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("server_legacy.p12");
        let mut buf = Vec::new();
        File::open(path)
            .unwrap()
            .read_to_end(&mut buf)
            .unwrap();
        
        let mut import_opts = Pkcs12ImportOptions::new();
        let imports = import_opts.passphrase("bark").import(&buf);
        match imports {
            Ok(i) => {
                for identity in i {
                    println!("label: {:?}", identity.label);
                    println!("trust: {}", identity.trust.is_some());
                }
                println!("ok");
            }
            Err(error) => {
                println!("{:?}", error);
            }
        }
    }
}
