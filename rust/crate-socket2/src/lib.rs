use std::net::SocketAddrV6;
use socket2::{Domain, Protocol, Socket, Type};

#[test]
fn ipv6() {
    let socket = Socket::new(Domain::IPV6, Type::DGRAM, Some(Protocol::UDP)).unwrap();
    let r = socket.set_only_v6(true);
    println!("Socket::new : {:?}", r);

    let addr = "[::]:0".parse::<SocketAddrV6>().unwrap();
    let r = socket.bind(&addr.into());
    println!("Socket::bind : {:?}", r);
}
