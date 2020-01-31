use std::net::ToSocketAddrs;
use trust_dns_resolver::Resolver;
use trust_dns_resolver::config::{ResolverConfig, ResolverOpts, LookupIpStrategy};

fn main() {
    ipv4();
    ipv6();
}

// 名前解決は標準ライブラリで可能だけど、明示的にIPv6アドレス(AAAAレコード)を取ることはできない？
fn ipv4() {
    // ポート番号を指定しないとエラーになる
    let host = "example.com:0";

    let r = match host[..].to_socket_addrs() {
        Ok(list) => {
            Ok(list.map(|socket_addr| {
                socket_addr.ip()
            }).collect::<Vec<_>>())
        },
        Err(e) => Err(e)
    }.map_err(|e| println!("{:?}", e)).unwrap();

    println!("{:?}", r);
}

// IPv6アドレスを取りたい場合は trust-dns-resolverを使う
// https://crates.io/crates/trust-dns-resolver
fn ipv6() {
    // FQDN(末尾にドット)を指定する
    let host = "example.com.";

    let resolver = Resolver::new(
        ResolverConfig::default(),
        ResolverOpts {
            ip_strategy: LookupIpStrategy::Ipv6Only, // IPv6だけを取る
            ..ResolverOpts::default()
        }
    ).unwrap();
    let response = resolver.lookup_ip(host).unwrap();
    let address = response.iter().next().expect("no addresses returned!");

    println!("{:?}", address);
}
