mod value_object {
    pub const MAX_NODES_PER_BUCKET: usize = 16;

    // `[0, MAX_NODES_PER_BUCKET)`.
    #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct Position {
        inner: usize,
    }

    impl Position {
        fn new(inner: usize) -> Result<Self, String> {
            if inner >= MAX_NODES_PER_BUCKET {
                Err("invalid pos value".to_owned())
            } else {
                Ok(Self { inner })
            }
        }
    }

    mod test {
        use super::*;

        #[test]
        fn position() {
            assert!(Position::new(10).is_ok());
            assert!(Position::new(17).is_err());
        }
    }
}
