use crate::rust_pb::person::Person;
use protobuf::Message;
use std::io::Write;
use crate::rust_pb::tracing::{Log, Log_SendWhoAreYou};
use protobuf::well_known_types::Timestamp;
use chrono::prelude::*;

const FILE: &str = "person.log";
const FILE_TRACING: &str = "tracing.log";

#[test]
fn write_person() {
    if std::path::Path::new(FILE).exists() {
        std::fs::remove_file(FILE).unwrap();
    }

    {
        let person = person("foo");
        write(person.write_length_delimited_to_bytes().unwrap(), FILE);
    }

    {
        let person = person("bar");
        write(person.write_length_delimited_to_bytes().unwrap(), FILE);
    }

    fn person(name: &str) -> Person {
        let mut person = Person::new();
        person.set_name(name.into());
        person
    }
}

#[test]
fn write_tracing() {
    if std::path::Path::new(FILE_TRACING).exists() {
        std::fs::remove_file(FILE_TRACING).unwrap();
    }

    {
        let log = log();
        write(log.write_length_delimited_to_bytes().unwrap(), FILE_TRACING);
    }

    {
        let log = log();
        write(log.write_length_delimited_to_bytes().unwrap(), FILE_TRACING);
    }

    fn log() -> Log {
        let mut send_whoareyou = Log_SendWhoAreYou::new();
        send_whoareyou.set_sender("node#0".into());
        send_whoareyou.set_recipient("node#1".into());
        send_whoareyou.set_id_nonce(111);
        send_whoareyou.set_enr_seq(222);

        let time = Local::now();
        let timestamp_nanos = time.timestamp_nanos();
        let seconds = timestamp_nanos / 1_000_000_000;
        let nano = timestamp_nanos - (seconds * 1_000_000_000);
        // println!("timestamp_nanos: {:?}", timestamp_nanos);
        // println!("seconds: {:?}", seconds);
        // println!("nano: {:?}", nano);

        let mut timestamp = Timestamp::new();
        timestamp.set_seconds(seconds);
        timestamp.set_nanos(std::convert::TryFrom::try_from(nano).unwrap());
        // println!("timestamp: {:?}", timestamp);

        let mut log = Log::new();
        log.set_timestamp(timestamp);
        log.set_send_whoareyou(send_whoareyou);
        log
    }
}

fn write(bytes: Vec<u8>, path: &str) {
    println!("bytes: {:?}", bytes);

    let mut file = std::fs::OpenOptions::new()
        .append(true)
        // 書き換える場合
        // .write(true)
        // .truncate(true)
        .create(true)
        .open(path)
        .unwrap();
    file.write_all(&bytes).unwrap();
    file.flush().unwrap();
}
