use std::net::UdpSocket;

pub fn serve(address: &str) -> Result<(), failure::Error> {
    let server_socket = UdpSocket::bind(address)?;

    loop {
        // UDPはTCPと違って、データがきたら送信元に対してただデータをお繰り返しているだけ
        // UDPでは1つのソケットが全てのクライアントとの通信を捌く
        let mut buf = [0u8; 1024];
        let (size, src) = server_socket.recv_from(&mut buf)?;
        debug!("Handling data from {}", src);
        print!("{}", std::str::from_utf8(&buf[..size])?);
        server_socket.send_to(&buf, src)?;
    }
}