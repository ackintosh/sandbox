use std::net::{IpAddr, Ipv4Addr};

#[test]
fn ipaddr() {
    let localhost_v4 = IpAddr::V4(Ipv4Addr::LOCALHOST);
    println!("{localhost_v4}");
}

#[test]
fn ipv4() {
    let addr = "127.0.0.1".parse::<Ipv4Addr>().unwrap();
    println!("{}", addr);
}
