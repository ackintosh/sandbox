// use std::net::{IpAddr, Ipv6Addr, TcpStream};

use std::net::TcpListener;

// IPv6が有効かどうかを判定する
#[test]
fn test_ipv6() {
    let r = TcpListener::bind("[::]:0");
    println!("{:?}", r);
    drop(r);

    // ローカルで何かデーモンプログラムが起動していないと判定できないかもしれない
    // if let Ok(_) = TcpStream::connect((IpAddr::V6(Ipv6Addr::LOCALHOST), 0)) {
    //     println!("ipv6 is available");
    // } else {
    //     println!("ipv6 isn't available");
    // }
}
