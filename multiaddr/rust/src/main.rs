use parity_multiaddr::Multiaddr;

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
}
