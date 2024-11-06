#[cfg(test)]
mod tests {
    use std::env;
    use std::fs::File;
    use std::io::Read;
    use std::path::PathBuf;
    use native_tls::Identity;

    #[test]
    fn it_works() {
        let path = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("server.p12");
        let mut buf = Vec::new();
        File::open(path)
            .unwrap()
            .read_to_end(&mut buf)
            .unwrap();
        let password = "bark";

        let result = Identity::from_pkcs12(&buf, password);
        if result.is_ok() {
            println!("ok");
        } else {
            println!("ng");
        }
    }
}
