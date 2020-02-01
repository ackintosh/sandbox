use std::net::ToSocketAddrs;
use trust_dns_resolver::Resolver;
use trust_dns_resolver::config::{ResolverConfig, ResolverOpts, LookupIpStrategy};

fn main() {
    libstd();
//    trust_dns_resolver();
}

// 名前解決は標準ライブラリで可能
fn libstd() {
    // ポート番号を指定しないとエラーになる
    let host = "example.com:0";
    // let host = "localhost:0";

    let addrs = match host[..].to_socket_addrs() {
        Ok(list) => {
            println!("{:?}", list);
            Ok(list.map(|socket_addr| {
                socket_addr.ip()
            }).collect::<Vec<_>>())
        },
        Err(e) => Err(e)
    }.map_err(|e| println!("{:?}", e)).unwrap();

    // 明示的にIPv6だけを取得することはできないので、条件分岐させる必要あり
    for addr in addrs {
        if addr.is_ipv4() {
            println!("IPv4: {}", addr);
        } else if addr.is_ipv6() {
            println!("IPv6: {}", addr);
        }
    }
}

// https://crates.io/crates/trust-dns-resolver
//
// Can't create custom ResolverOpts · Issue #1004 · bluejekyll/trust-dns
// https://github.com/bluejekyll/trust-dns/issues/1004
//fn trust_dns_resolver() {
//    // FQDN(末尾にドット)を指定する
//    let host = "example.com.";
//
//    let resolver = Resolver::new(
//        ResolverConfig::default(),
//        ResolverOpts {
//            ip_strategy: LookupIpStrategy::Ipv6Only, // IPv6だけを取る
//            ..ResolverOpts::default()
//        }
//    ).unwrap();
//    let response = resolver.lookup_ip(host).unwrap();
//    let address = response.iter().next().expect("no addresses returned!");
//
//    println!("{:?}", address);
//}
