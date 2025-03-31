
#[cfg(test)]
mod tests {
    // use std::fs::{set_permissions, Permissions};
    use std::io::Write;
    // use std::os::unix::fs::PermissionsExt;
    // use std::path::Path;
    use logroller::{LogRollerBuilder, Rotation, RotationSize};

    #[test]
    fn it_works() {
        // let path = Path::new("./logs/logger.log");
        // set_permissions(path, Permissions::from_mode(0o600)).unwrap();
        
        let mut logger = LogRollerBuilder::new("./logs", "logger.log")
            .rotation(Rotation::SizeBased(RotationSize::Bytes(50)))
            .max_keep_files(3)
            // .file_mode(0o600)
            .build().unwrap();

        writeln!(logger, "This is an info message").unwrap();
        writeln!(logger, "This is a warning message").unwrap();
        writeln!(logger, "This is an error message").unwrap();
    }
}
