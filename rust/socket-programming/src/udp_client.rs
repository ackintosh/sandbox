use std::net::UdpSocket;

pub fn communicate(address: &str) -> Result<(), failure::Error> {
    // 0番ポートを指定することでOSが空いているポートを選んでくれる
    let socket = UdpSocket::bind("127.0.0.1:0")?;

    loop {
        let mut input = String::new();
        std::io::stdin().read_line(&mut input)?;
        socket.send_to(input.as_bytes(), address)?;

        // バッファサイズの1024は適当
        // 1025バイト以降のデータは破棄されてしまう
        let mut buffer = [0u8; 1024];
        socket.recv_from(&mut buffer).expect("failed to receive");
        print!(
            "{}",
            std::str::from_utf8(&buffer).expect("failed to convert to String")
        );
    }
}
