use std::net::Ipv4Addr;

#[test]
fn ipv4() {
    let addr = "127.0.0.1".parse::<Ipv4Addr>().unwrap();
    println!("{}", addr);
}
