// use std::net::{IpAddr, Ipv6Addr, TcpStream};

use std::net::{IpAddr, Ipv6Addr, SocketAddr, TcpListener, TcpStream, UdpSocket};

// IPv6が有効かどうかを判定する
// cargo test -p primitives test_ipv6 -- --show-output
#[test]
fn test_ipv6() {

    let listener = TcpListener::bind("[::]:0").unwrap();
    // listener.set_only_v6(true).unwrap(); // `Err` value: Os { code: 22, kind: InvalidInput, message: "Invalid argument" }'
    let addr = listener.local_addr().unwrap();
    println!("socketaddr: {:?}", addr);
    if let SocketAddr::V6(_) = addr {
        println!("ipv6");
    } else {
        println!("ipv4");
    }

    // ローカルで何かデーモンプログラムが起動していないと判定できないかもしれない
    // if let Ok(_) = TcpStream::connect((IpAddr::V6(Ipv6Addr::LOCALHOST), 0)) {
    //     println!("ipv6 is available");
    // } else {
    //     println!("ipv6 isn't available");
    // }
}
