use crate::rust_pb::person::Person;
use protobuf::Message;
use std::io::Write;

#[test]
fn test() {
    let mut person = Person::new();
    person.set_name("foo".into());
    println!("person: {:?}", person);

    let bytes = person.write_to_bytes().unwrap();
    println!("{:?}", bytes);

    let mut file = std::fs::OpenOptions::new()
        .append(true)
        .open("person.bin")
        .unwrap();
    file.write_all(&bytes).unwrap();
    file.flush().unwrap();
}
