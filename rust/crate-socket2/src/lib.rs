use std::net::SocketAddrV6;
use socket2::{Domain, Protocol, Socket, Type};

// cargo test --package crate-socket2 --lib test_ipv6 -- --show-output
#[test]
fn test_ipv6() {
    let socket = Socket::new(Domain::IPV6, Type::DGRAM, Some(Protocol::UDP)).unwrap();
    let r = socket.set_only_v6(true);
    println!("Socket::new : {:?}", r);

    let addr = "[::]:0".parse::<SocketAddrV6>().unwrap();
    let r = socket.bind(&addr.into());
    println!("Socket::bind : {:?}", r);
    let ad = socket.local_addr();
    println!("local_addr: {:?}", ad.unwrap().as_socket_ipv6());
}
