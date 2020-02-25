use parity_multiaddr::{Multiaddr, Protocol};
use futures::prelude::stream::FuturesOrdered;
use futures::{Future, FutureExt};
use futures::future::BoxFuture;
use futures::stream::StreamExt;

fn main() {
    let mut addr: Multiaddr = "/ip4/127.0.0.1/tcp/2000".parse().unwrap();
    println!("{:?}", addr);
    // "/ip4/127.0.0.1/tcp/2000"

    let addr2: Multiaddr = "/udt/sctp/5678".parse().unwrap();
    println!("{:?}", addr2);
    // "/udt/sctp/5678"

    addr2.iter().for_each(|protocol| addr.push(protocol));
    println!("{:?}", addr);
    // "/ip4/127.0.0.1/tcp/2000/udt/sctp/5678"

    let addr3: Multiaddr = "".parse().unwrap(); // 空
    println!("{:?}", addr3);
    // ""

    let addrs: Vec<Multiaddr> = vec![
        "/ip4/127.0.0.1/tcp/2000".parse().unwrap(),
        "/udt/sctp/5678".parse().unwrap()
    ];

    let concat = addrs.iter().fold(Multiaddr::empty(), |mut addr, next| {
        next.iter().for_each(|protocol| addr.push(protocol));
        addr
    });
    println!("{:?}", concat);
    // "/ip4/127.0.0.1/tcp/2000/udt/sctp/5678"

    test_struct();
}


fn test_struct() {
    let s = TestStruct::new(100);
    let addr: Multiaddr = "/ip4/127.0.0.1/tcp/2000".parse().unwrap();
    s.test(addr);
}

struct TestStruct {
    inner: i32,
}

impl TestStruct {
    fn new(inner: i32) -> Self {
        Self { inner }
    }

    fn test(self, addr: Multiaddr) -> BoxFuture<'static, Vec<Multiaddr>> {
        let mut futs = FuturesOrdered::new();
        for (_i, n) in addr.iter().enumerate() {
            let f = match n {
                Protocol::Ip4(_) => {
                    println!("{:?}", n);
                    test_future()
                }
                cmp => {
                    println!("{:?}", addr);
                    test_future()
                }
            };
            futs.push(f);
        }
        let t = futs.collect::<Vec<_>>().then(|a| {
            println!("{:?}", a);
            async move {
                a
            }
        });
       t.boxed()
    }
}

async fn test_future() -> Multiaddr {
    Multiaddr::empty()
}
