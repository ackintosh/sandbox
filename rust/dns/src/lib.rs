use std::str::FromStr;
use std::net::ToSocketAddrs;
// use futures::TryFutureExt;
use trust_dns_resolver::{Resolver, Name};
use trust_dns_resolver::config::{ResolverConfig, ResolverOpts, LookupIpStrategy};
use trust_dns_client::udp::{UdpClientConnection, UdpClientStream};
use trust_dns_client::client::{SyncClient, Client, AsyncClient, ClientHandle};
use trust_dns_resolver::proto::rr::{DNSClass, RecordType, Record, RData};
use trust_dns_resolver::proto::op::Message;

#[test]
fn test() {
    libstd();
    trust_dns_resolver();
    txt();
    async_usage();
    // async_usage2();
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


    let opts = ResolverOpts {
        ip_strategy: LookupIpStrategy::Ipv6Only,
        ..ResolverOpts::default()
    };

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

    // 同期処理のクライアント
    let client = SyncClient::new(conn);

    // TXTレコードを取得する
    let name = Name::from_str("_dnsaddr.bootstrap.libp2p.io").unwrap();
    let response = client.query(&name, DNSClass::IN, RecordType::TXT).unwrap();
    // println!("{:?}", response);
    let answers: &[Record] = response.answers();

    // *素朴にループする*
    for answer in answers.iter() {
        if let &RData::TXT(ref txt) = answer.rdata() {
            for d in txt.iter() {
                println!("{}", std::str::from_utf8(d).unwrap());
            }
        } else {
            assert!(false, "unexpected result");
        }
    }

    // *txtレコードの文字列をベクターにまとめる*
    let txt_record_strs = answers.iter()
        .filter_map(|record| {
            if let RData::TXT(txt) = record.rdata() {
                Some(txt.iter())
            } else {
                None
            }
        })
        .flatten()
        .map(|a| {
            // println!("{}", std::str::from_utf8(a).unwrap());
            std::str::from_utf8(a).unwrap()
        })
        .collect::<Vec<_>>();
     println!("{:?}", txt_record_strs);
     // [
     //   "dnsaddr=/dnsaddr/ams-2.bootstrap.libp2p.io/tcp/4001/ipfs/QmbLHAnMoJPWSCR5Zhtx6BHJX9KiKNN6tpvbUcqanj75Nb",
     //   "dnsaddr=/dnsaddr/ewr-1.bootstrap.libp2p.io/tcp/4001/ipfs/QmQCU2EcMqAqQPR2i9bChDtGNJchTbq5TbXJJ16u19uLTa",
     //   "dnsaddr=/dnsaddr/nrt-1.bootstrap.libp2p.io/tcp/4001/ipfs/QmcZf59bWwK5XFi76CZX8cbJ4BhTzzA3gU1ZjYZcYW3dwt",
     //   "dnsaddr=/dnsaddr/sjc-1.bootstrap.libp2p.io/tcp/4001/ipfs/QmNnooDu7bfjPFoTZYxMNLWUQJyrVwtbZg5gBMjTezGAJN"
     // ]
}

fn async_usage() {
    let stream = UdpClientStream::<tokio::net::UdpSocket>::new(([8,8,8,8], 53).into());
    let client = AsyncClient::connect(stream);

    let mut runtime = tokio::runtime::Runtime::new().unwrap();
    let (mut client, bg) = runtime.block_on(client).expect("connection failed");

    runtime.spawn(bg);

    let name = Name::from_str("_dnsaddr.bootstrap.libp2p.io").unwrap();
    let query = client.query(name, DNSClass::IN, RecordType::TXT);

    let response = runtime.block_on(query).unwrap();

    println!("{:?}", response);
}

// fn async_usage2() {
//     let stream = UdpClientStream::<tokio::net::UdpSocket>::new(([8,8,8,8], 53).into());
//     let client = AsyncClient::connect(stream)
//         .and_then(|(async_client, dns_exchange_background)| async {
//             let m: Message = s.into();
//             println!("{:?}", m);
//             Ok(s)
//         });
//
//     let mut runtime = tokio::runtime::Runtime::new().unwrap();
//     runtime.block_on(client);
// }