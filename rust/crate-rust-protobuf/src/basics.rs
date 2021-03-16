use crate::rust_pb::person::Person;
use protobuf::Message;
use std::io::Write;

const FILE: &str = "person.log";

#[test]
fn test() {
    if std::path::Path::new(FILE).exists() {
        std::fs::remove_file(FILE).unwrap();
    }

    {
        let person = person("foo");
        write(person.write_length_delimited_to_bytes().unwrap());
    }

    {
        let person = person("bar");
        write(person.write_length_delimited_to_bytes().unwrap());
    }
}

fn person(name: &str) -> Person {
    let mut person = Person::new();
    person.set_name(name.into());
    person
}

fn write(bytes: Vec<u8>) {
    println!("bytes: {:?}", bytes);

    let mut file = std::fs::OpenOptions::new()
        .append(true)
        // 書き換える場合
        // .write(true)
        // .truncate(true)
        .create(true)
        .open(FILE)
        .unwrap();
    file.write_all(&bytes).unwrap();
    file.flush().unwrap();
}
