use crate::packet::TcpPacket;
use pnet::packet::ip::IpNextHeaderProtocols;
use pnet::packet::Packet;
use pnet::transport;
use pnet::transport::{TransportChannelType, TransportProtocol, TransportSender};
use pnet::util::ipv4_checksum;
use std::fmt::{Display, Formatter};
use std::net::{IpAddr, Ipv4Addr};

const SOCKET_BUFFER_SIZE: usize = 4380;

// TCPのエンドポイントとなるソケットは通信するホスト間で一対一対応をするので，
// ローカルのIPアドレス，リモートのIPアドレス，ローカルのポート番号，リモートのポート番号の4つの情報から一意に定まる
// このペアはSocketId構造体として定義し，コネクションの特定に利用する
// このうち，どれか1つでも異なる値になれば別のアプリケーション（プロセス）間が通信していることになる
#[derive(Debug, Hash, Eq, PartialEq, Clone, Copy)]
pub struct SocketId(pub Ipv4Addr, pub Ipv4Addr, pub u16, pub u16);

pub struct Socket {
    pub local_addr: Ipv4Addr,
    pub remote_addr: Ipv4Addr,
    pub local_port: u16,
    pub remote_port: u16,
    pub send_param: SendParam,
    pub recv_param: RecvParam,
    pub status: TcpStatus,
    pub sender: TransportSender,
}

impl Socket {
    pub fn new(
        local_addr: Ipv4Addr,
        remote_addr: Ipv4Addr,
        local_port: u16,
        remote_port: u16,
        status: TcpStatus,
    ) -> std::io::Result<Self> {
        let (sender, _) = transport::transport_channel(
            65535,
            TransportChannelType::Layer4(TransportProtocol::Ipv4(IpNextHeaderProtocols::Tcp)),
        )?;

        Ok(Self {
            local_addr,
            remote_addr,
            local_port,
            remote_port,
            send_param: SendParam {
                unacked_seq: 0,
                initial_seq: 0,
                next: 0,
                window: SOCKET_BUFFER_SIZE as u16,
            },
            recv_param: RecvParam {
                initial_seq: 0,
                next: 0,
                window: SOCKET_BUFFER_SIZE as u16,
                tail: 0,
            },
            status,
            sender,
        })
    }

    pub fn send_tcp_packet(
        &mut self,
        seq: u32,
        ack: u32,
        flag: u8,
        payload: &[u8],
    ) -> std::io::Result<usize> {
        let mut tcp_packet = TcpPacket::new(payload.len());
        tcp_packet.set_src(self.local_port);
        tcp_packet.set_dest(self.remote_port);
        tcp_packet.set_seq(seq);
        tcp_packet.set_ack(ack);
        tcp_packet.set_data_offset(5); // オプションフィールドは使わないので固定
        tcp_packet.set_flag(flag);
        tcp_packet.set_window_size(self.recv_param.window);
        tcp_packet.set_payload(payload);
        tcp_packet.set_checksum(ipv4_checksum(
            &tcp_packet.packet(),
            8,
            &[],
            &self.local_addr,
            &self.remote_addr,
            IpNextHeaderProtocols::Tcp,
        ));

        let sent_size = self
            .sender
            .send_to(tcp_packet, IpAddr::V4(self.remote_addr))
            .unwrap();

        dbg!("sent", &tcp_packet);
        Ok(sent_size)
    }

    pub fn get_socket_id(&self) -> SocketId {
        SocketId(
            self.local_addr,
            self.remote_addr,
            self.local_port,
            self.remote_port,
        )
    }
}

#[derive(Clone, Debug)]
pub struct SendParam {
    // SND.UNA
    // 送信後まだ ack されていない seq の先頭
    pub unacked_seq: u32,
    // SND.NXT
    // 次の送信
    pub next: u32,
    // SND.WND
    // 送信ウィンドウサイズ
    pub window: u16,
    // 初期送信 seq
    pub initial_seq: u32,
}

#[derive(Clone, Debug)]
pub struct RecvParam {
    // RCV.NXT
    // 次に受信する seq
    pub next: u32,
    // RCV.WND
    // 受信ウィンドウ
    pub window: u16,
    // 初期受信 seq
    pub initial_seq: u32,
    // 受信 seq の最後尾
    pub tail: u32,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TcpStatus {
    Listen,
    SynSent,
    SynRcvd,
    Established,
    FinWait1,
    FinWait2,
    TimeWait,
    CloseWait,
    LastAck,
}

impl Display for TcpStatus {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TcpStatus::Listen => write!(f, "LISTEN"),
            TcpStatus::SynSent => write!(f, "SYNSENT"),
            TcpStatus::SynRcvd => write!(f, "SYNRCVD"),
            TcpStatus::Established => write!(f, "ESTABLISHED"),
            TcpStatus::FinWait1 => write!(f, "FINWAIT1"),
            TcpStatus::FinWait2 => write!(f, "FINWAIT2"),
            TcpStatus::TimeWait => write!(f, "TIMEWAIT"),
            TcpStatus::CloseWait => write!(f, "CLOSEWAIT"),
            TcpStatus::LastAck => write!(f, "LASTACK"),
        }
    }
}
