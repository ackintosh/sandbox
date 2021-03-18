use crate::rust_pb::person::Person;
use protobuf::Message;
use std::io::Write;
use crate::rust_pb::tracing::{Log, Log_SendWhoAreYou, Log_NodeStarted};
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
        write(node_started("node#0").write_length_delimited_to_bytes().unwrap(), FILE_TRACING);
    }

    {
        write(node_started("node#1").write_length_delimited_to_bytes().unwrap(), FILE_TRACING);
    }

    {
        write(node_started("node#2").write_length_delimited_to_bytes().unwrap(), FILE_TRACING);
    }

    {
        let log = whoareyou("node#0", "node#1", 111, 222);
        write(log.write_length_delimited_to_bytes().unwrap(), FILE_TRACING);
    }

    {
        let log = whoareyou("node#1", "node#2", 111, 222);
        write(log.write_length_delimited_to_bytes().unwrap(), FILE_TRACING);
    }

    fn node_started(node_id: &str) -> Log {
        let mut node_started = Log_NodeStarted::new();
        node_started.set_node_id(node_id.into());

        let mut log = Log::new();
        log.set_timestamp(timestamp());
        log.set_node_started(node_started);

        log
    }

    fn whoareyou(sender: &str, recipient: &str, id_nonde: u64, enr_seq: u64) -> Log {
        let mut send_whoareyou = Log_SendWhoAreYou::new();
        send_whoareyou.set_sender(sender.into());
        send_whoareyou.set_recipient(recipient.into());
        send_whoareyou.set_id_nonce(id_nonde);
        send_whoareyou.set_enr_seq(enr_seq);


        let mut log = Log::new();
        log.set_timestamp(timestamp());
        log.set_send_whoareyou(send_whoareyou);
        log
    }

    fn timestamp() -> Timestamp {
        let time = Local::now();
        let timestamp_nanos = time.timestamp_nanos();
        let seconds = timestamp_nanos / 1_000_000_000;
        let nanos = timestamp_nanos - (seconds * 1_000_000_000);
        // println!("timestamp_nanos: {:?}", timestamp_nanos);
        // println!("seconds: {:?}", seconds);
        // println!("nano: {:?}", nano);

        let mut timestamp = Timestamp::new();
        timestamp.set_seconds(seconds);
        timestamp.set_nanos(std::convert::TryFrom::try_from(nanos).unwrap());
        // println!("timestamp: {:?}", timestamp);

        timestamp
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
