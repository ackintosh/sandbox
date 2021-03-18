// 参考
// https://github.com/stepancheg/rust-protobuf/blob/master/protobuf-test/build.rs

// extern crate protoc_rust;

use protoc_rust::Customize;

fn main() {
    let out_dir = "src/rust_pb";
    if std::path::Path::new(&out_dir).exists() {
        std::fs::remove_dir_all(&out_dir).unwrap();
    }
    std::fs::create_dir(&out_dir).unwrap();

    protoc_rust::Codegen::new()
        .out_dir(out_dir)
        .input("proto/person.proto")
        .input("proto/tracing.proto")
        .customize(Customize {
            gen_mod_rs: Some(true),
            ..Default::default()
        })
        .run()
        .unwrap();
}
