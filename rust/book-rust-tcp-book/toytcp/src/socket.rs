use std::net::{IpAddr, Ipv4Addr};
use pnet::packet::ip::IpNextHeaderProtocols;
use pnet::transport;
use pnet::transport::{TransportChannelType, TransportProtocol, TransportSender};
use crate::packet::TcpPacket;

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
    pub sender: TransportSender,
}

// TODO
pub enum TcpStatus {}

impl Socket {
    pub fn new(
        local_addr: Ipv4Addr,
        remote_addr: Ipv4Addr,
        local_port: u16,
        remote_port: u16,
    ) -> std::io::Result<Self> {
        let (sender, _) = transport::transport_channel(
            65535,
            TransportChannelType::Layer4(TransportProtocol::Ipv4(IpNextHeaderProtocols::Tcp))
        )?;

        Ok(Self {
            local_addr,
            remote_addr,
            local_port,
            remote_port,
            sender,
        })
    }

    pub fn send_tcp_packet(&mut self, flag: u8, payload: &[u8]) -> std::io::Result<usize> {
        let mut tcp_packet = TcpPacket::new(payload.len());
        tcp_packet.set_src(self.local_port);
        tcp_packet.set_dest(self.remote_port);
        tcp_packet.set_flag(flag);

        let sent_size = self.sender
            .send_to(tcp_packet, IpAddr::V4(self.remote_addr))
            .unwrap();

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
