use leveldb::database::kv::KV;
use leveldb::database::options::{Options, ReadOptions, WriteOptions};
use leveldb::database::Database;
use tempdir::TempDir;

#[test]
fn leveldb() {
    let tempdir = TempDir::new("leveldb").unwrap();
    let path = tempdir.path();

    let mut options = Options::new();
    options.create_if_missing = true;
    let mut database = match Database::open(path, options) {
        Ok(db) => db,
        Err(e) => panic!("failed to open database: {:?}", e),
    };

    let write_options = WriteOptions::new();
    match database.put(write_options, 1, &[1]) {
        Ok(_) => (),
        Err(e) => panic!("failed to write to database: {:?}", e),
    };

    let read_options = ReadOptions::new();
    match database.get(read_options, 1) {
        Ok(data) => {
            assert!(data.is_some());
            assert_eq!(data, Some(vec![1]));
        }
        Err(e) => panic!("failed reading data: {:?}", e),
    }
}
