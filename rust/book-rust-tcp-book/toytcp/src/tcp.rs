use std::collections::HashMap;
use std::net::Ipv4Addr;
use std::ops::Range;
use crate::socket::{Socket, SocketId};

const UNDETERMINED_ID_ADDR: Ipv4Addr = Ipv4Addr::new(0, 0, 0, 0);
const UNDETERMINED_PORT: u16 = 0;
const MAX_TRANSMISSION: u8 = 5;
const RETRANSMISSION_TIMEOUT: u64 = 3;
const MSS: usize = 1460;
const PORT_RANGE: Range<u16> = 40000..60000;

pub struct ToyTcp {
    // Socketのハッシュテーブルを保持し、現在利用しているソケットの管理を行う
    sockets: HashMap<SocketId, Socket>,
}

impl ToyTcp {
    pub fn new() -> Self {
        Self {
            sockets: HashMap::new(),
        }
    }

    fn select_unused_port(&self) -> std::io::Result<u16> {
        // 取り急ぎ固定値
        Ok(33445)
    }

    pub fn connect(&self, addr: Ipv4Addr, port: u16) -> std::io::Result<SocketId> {
        // let mut rng = rand::thread_rng();

        let mut socket = Socket::new(
            addr.clone(),
            addr, // 同一ホストで実行するだけなので同じアドレスをセットしている
            self.select_unused_port()?,
            port,
        )?;

        // スリーウェイハンドシェイクの最初の SYN セグメントを送信する
        socket.send_tcp_packet(crate::tcpflags::SYN, &[])?;

        Ok(socket.get_socket_id())
    }

}

// 見本コードにあるけど未使用
// fn get_source_addr_to(_addr: Ipv4Addr) -> std::io::Result<Ipv4Addr> {
//     Ok("10.0.0.1".parse().unwrap())
// }
