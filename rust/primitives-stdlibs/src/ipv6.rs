// use std::net::{IpAddr, Ipv6Addr, TcpStream};

use std::net::{SocketAddr, TcpListener};

// IPv6が有効かどうかを判定する
#[test]
fn test_ipv6() {
    let r = TcpListener::bind("[::1]:0");
    println!("result: {:?}", r);
    match r {
        Ok(listener) => {
            let addr = listener.local_addr().unwrap();
            println!("socketaddr: {:?}", addr);
            if let SocketAddr::V6(_) = addr {
                println!("ipv6");
            } else {
                println!("ipv4");
            }
        }
        Err(_) => {
            println!("ipv6 isn't available");
        }
    }

    // ローカルで何かデーモンプログラムが起動していないと判定できないかもしれない
    // if let Ok(_) = TcpStream::connect((IpAddr::V6(Ipv6Addr::LOCALHOST), 0)) {
    //     println!("ipv6 is available");
    // } else {
    //     println!("ipv6 isn't available");
    // }
}
