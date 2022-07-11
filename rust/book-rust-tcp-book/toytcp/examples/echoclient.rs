use std::env;
use std::net::Ipv4Addr;
use book_rust_tcp_book_toytcp::tcp::ToyTcp;

// 実行例:
// * 適当なサーバとして netcat を利用する
// nc -l localhost 40000
// * 接続する
// cargo run --example echoclient 127.0.0.1 40000

fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();
    let addr: Ipv4Addr = args[1].parse().expect("valid ipv4 address");
    let port: u16 = args[2].parse().expect("valid port number");
    echo_client(addr, port)?;

    Ok(())
}

fn echo_client(remote_addr: Ipv4Addr, remote_port: u16) -> std::io::Result<()> {
    let toy_tcp = ToyTcp::new();
    let socket_id = toy_tcp.connect(remote_addr, remote_port)?;

    println!("Connected: {:?}", socket_id);
    Ok(())
}
