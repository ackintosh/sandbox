#[cfg(test)]
mod tests {
    use std::env;
    use std::fs::File;
    use std::io::Read;
    use std::path::PathBuf;
    use security_framework::import_export::Pkcs12ImportOptions;

    #[test]
    fn it_works() {
        let path = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("server.p12");
        let mut buf = Vec::new();
        File::open(path)
            .unwrap()
            .read_to_end(&mut buf)
            .unwrap();
        
        let mut import_opts = Pkcs12ImportOptions::new();
        let imports = import_opts.passphrase("bark").import(&buf);
        match imports {
            Ok(imported_identity) => {
                println!("ok");
            }
            Err(error) => {
                println!("{:?}", error);
            }
        }
    }
}
