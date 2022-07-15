use crate::packet::TcpPacket;
use crate::socket::{Socket, SocketId, TcpStatus};
use crate::tcpflags;
use pnet::packet::ip::IpNextHeaderProtocols;
use pnet::transport;
use pnet::transport::TransportChannelType;
use rand::Rng;
use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::ops::Range;
use std::sync::{Arc, Condvar, Mutex, RwLock};

const UNDETERMINED_ID_ADDR: Ipv4Addr = Ipv4Addr::new(0, 0, 0, 0);
const UNDETERMINED_PORT: u16 = 0;
const MAX_TRANSMISSION: u8 = 5;
const RETRANSMISSION_TIMEOUT: u64 = 3;
const MSS: usize = 1460;
const PORT_RANGE: Range<u16> = 40000..60000;

// Socketのハッシュテーブルを保持し、現在利用しているソケットの管理を行う
pub struct ToyTcp {
    // ソケットのハッシュテーブルは下記3つのスレッド間で共有され、全てのスレッドから書き込みが行われる
    // * 送信スレッド（メインスレッド）
    // * 受信スレッド
    // * 再相関利用のタイマースレッド
    // そのため、RwLockでハッシュテーブルを保護する
    sockets: RwLock<HashMap<SocketId, Socket>>,
    // event_condvarは条件変数を扱う
    // 「コネクションを確立した」「ペイロードを受信した」といったイベントを他のスレッドから受け取るまで待機するために利用する
    event_condvar: (Mutex<Option<TcpEvent>>, Condvar),
}

impl ToyTcp {
    pub fn new() -> Arc<Self> {
        let sockets = RwLock::new(HashMap::new());
        let toy_tcp = Arc::new(Self {
            sockets,
            event_condvar: (Mutex::new(None), Condvar::new()),
        });

        // パケット受信用スレッドを起動する
        let cloned_toy_tcp = toy_tcp.clone();
        std::thread::spawn(move || {
            cloned_toy_tcp.receive_handler().unwrap();
        });

        toy_tcp
    }

    fn select_unused_port(&self) -> std::io::Result<u16> {
        let mut rng = rand::thread_rng();

        for _ in 0..(PORT_RANGE.end - PORT_RANGE.start) {
            let local_port = rng.gen_range(PORT_RANGE);
            let sockets = self.sockets.read().unwrap();

            // 使用するローカルポートが他のソケットと重複していると、コネクションを一意に特定できない
            if sockets.keys().all(|k| k.2 != local_port) {
                return Ok(local_port);
            }
        }
        anyhow::bail!("no available port found.");
    }

    // 指定された宛先とコネクションを確立し、接続済みソケットのSocketIdを返す
    pub fn connect(&self, remote_addr: Ipv4Addr, port: u16) -> std::io::Result<SocketId> {
        let mut socket = Socket::new(
            remote_addr.clone(), // 同一ホストで実行するだけなので同じアドレスをセットしている
            remote_addr,
            self.select_unused_port()?,
            port,
            TcpStatus::SynSent,
        )?;

        // スリーウェイハンドシェイクの最初の SYN セグメントを送信してアクティブオープンを試みる
        let mut rng = rand::thread_rng();
        // 初期シーケンス番号は乱数で選ぶ
        // * 利用されたコネクションのシーケンス番号との混乱を避けるため
        // * TCPシーケンス番号予測攻撃を避けるため
        socket.send_param.initial_seq = rng.gen_range(1..1 << 31);
        socket.send_tcp_packet(socket.send_param.initial_seq, 0, crate::tcpflags::SYN, &[])?;
        socket.send_param.unacked_seq = socket.send_param.initial_seq;
        socket.send_param.next = socket.send_param.initial_seq + 1;

        let socket_id = {
            let mut sockets = self.sockets.write().unwrap();
            let socket_id = socket.get_socket_id();
            sockets.insert(socket_id, socket);
            socket_id
        };

        self.wait_event(socket_id, TcpEventKind::ConnectionCompleted);
        Ok(socket.get_socket_id())
    }

    // 受信スレッド用の関数
    fn receive_handler(&self) -> std::io::Result<()> {
        dbg!("begin recv thread");

        let (_, mut receiver) = transport::transport_channel(
            65535,
            // IPアドレスが必要なので、IPパケットレベルで取得する
            TransportChannelType::Layer3(IpNextHeaderProtocols::Tcp),
        )
        .unwrap();

        let mut packet_iter = transport::ipv4_packet_iter(&mut receiver);

        loop {
            let (packet, remote_addr) = match packet_iter.next() {
                Ok((p, r)) => (p, r),
                Err(e) => {
                    println!("receive_handler: {:?}", e);
                    continue;
                }
            };

            let local_addr = packet.get_destination();
            let packet: TcpPacket = {
                // pnetのTcpPacketを生成する
                let pnet_tcp_packet = match pnet::packet::tcp::TcpPacket::new(packet.payload()) {
                    Some(p) => p,
                    None => continue,
                };
                pnet_tcp_packet.into()
            };

            let remote_addr = match remote_addr {
                IpAddr::V4(addr) => addr,
                IpAddr::V6(_) => unreachable!(), // ipv4のみ利用している
            };

            let mut sockets = self.sockets.write().unwrap();
            let socket = match sockets.get_mut(&SocketId(
                local_addr,
                remote_addr,
                packet.get_dest(),
                packet.get_src(),
            )) {
                Some(socket) => socket, // 接続済みソケット
                None => match sockets.get_mut(&SocketId(
                    local_addr,
                    UNDETERMINED_ID_ADDR,
                    packet.get_dest(),
                    UNDETERMINED_PORT,
                )) {
                    Some(socket) => socket, // リスニングソケット
                    None => continue,       // どのソケットにも該当しないものは無視
                },
            };

            if !packet.is_correct_checksum(local_addr, remote_addr) {
                dbg!("invalid checksum");
                continue;
            }

            // let socket_id = socket.get_socket_id();
            if let Err(e) = match socket.status {
                // TcpStatus::Listen => {}
                TcpStatus::SynSent => self.synsent_handler(socket, &packet),
                _ => todo!(),
                // TcpStatus::SynRcvd => {}
                // TcpStatus::Established => {}
                // TcpStatus::FinWait1 => {}
                // TcpStatus::FinWait2 => {}
                // TcpStatus::TimeWait => {}
                // TcpStatus::CloseWait => {}
                // TcpStatus::LastAck => {}
            } {
                dbg!(e);
            }
        }
    }

    fn wait_event(&self, sock_id: SockID, kind: TcpEventKind) {
        todo!()
    }

    // SYSSENT状態のソケットに到着したパケットの処理を行う
    fn synsent_handler(&self, socket: &mut Socket, packet: &TcpPacket) -> std::io::Result<()> {
        dbg!("synsent handler");

        todo!();

        Ok(())
    }
}

// TODO
struct TcpEvent {}

enum TcpEventKind {
    ConnectionCompleted,
}

// 見本コードにあるけど未使用
// fn get_source_addr_to(_addr: Ipv4Addr) -> std::io::Result<Ipv4Addr> {
//     Ok("10.0.0.1".parse().unwrap())
// }
