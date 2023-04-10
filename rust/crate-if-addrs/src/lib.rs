#[test]
fn test() {
    // ネットワーク・インターフェースを取得する
    let interfaces = if_addrs::get_if_addrs().unwrap();

    for i in interfaces.iter() {
        println!("{i:?}, is_loopback:{}, is_ipv6:{}", i.is_loopback(), i.addr.ip().is_ipv6());
    }
}