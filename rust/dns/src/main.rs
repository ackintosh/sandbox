use std::str::FromStr;
use std::net::ToSocketAddrs;
use trust_dns_resolver::{Resolver, Name};
use trust_dns_resolver::config::{ResolverConfig, ResolverOpts, LookupIpStrategy};
use trust_dns_client::udp::UdpClientConnection;
use trust_dns_client::client::{SyncClient, Client};
use trust_dns_resolver::proto::rr::{DNSClass, RecordType, Record, RData};

fn main() {
    libstd();
    trust_dns_resolver();
    txt();
}

// 名前解決は標準ライブラリで可能
fn libstd() {
    println!("/// libstd ///");

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
fn trust_dns_resolver() {
    println!("/// trust_dns_resolver ///");

    // FQDN(末尾にドット)を指定する
    let host = "example.com.";

    let mut opts = ResolverOpts::default();
    opts.ip_strategy = LookupIpStrategy::Ipv6Only;
    let resolver = Resolver::new(
        ResolverConfig::default(),
        opts
    ).unwrap();
    let response = resolver.lookup_ip(host).unwrap();
    let address = response.iter().next().expect("no addresses returned!");

    println!("{:?}", address);
}

// 汎用的なクエリには trust-dns-client を使う
// https://crates.io/crates/trust-dns-client
fn txt() {
    println!("/// txt ///");

    let name_server = "8.8.8.8:53".parse().unwrap();
    let conn = UdpClientConnection::new(name_server).unwrap();
    let client = SyncClient::new(conn);

    // TXTレコードを取得する
    let name = Name::from_str("_dnsaddr.bootstrap.libp2p.io").unwrap();
    let response = client.query(&name, DNSClass::IN, RecordType::TXT).unwrap();
    // println!("{:?}", response);
    let answers: &[Record] = response.answers();

    for answer in answers.iter() {
        if let &RData::TXT(ref txt) = answer.rdata() {
            for d in txt.iter() {
                println!("{}", std::str::from_utf8(d).unwrap());
            }
        } else {
            assert!(false, "unexpected result");
        }
    }
}
