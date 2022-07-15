use pnet::packet::ip::IpNextHeaderProtocols;
use pnet::packet::Packet;
use pnet::util;
use std::fmt::{Debug, Formatter};
use std::net::{IpAddr, Ipv4Addr};

const TCP_HEADER_SIZE: usize = 20;

#[derive(Clone)]
pub struct TcpPacket {
    buffer: Vec<u8>,
}

// TCP Header Format
//
//  0                   1                   2                   3
//  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
// |          Source Port          |        Destination Port       |
// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
// |                        Sequence Number                        |
// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
// |                     Acknowledgment Number                     |
// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
// | Offset|  Res. |     Flags     |             Window            |
// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
// |            Checksum           |         Urgent Pointer        |
// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
// |                    Options                    |    Padding    |
// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
impl TcpPacket {
    pub fn new(payload_len: usize) -> Self {
        Self {
            buffer: vec![0; TCP_HEADER_SIZE + payload_len],
        }
    }

    // ////////////////////////////////////////////////////////////////////////
    // Setters
    // ////////////////////////////////////////////////////////////////////////

    pub fn set_src(&mut self, port: u16) {
        // `port.to_be_bytes()` としている箇所は、ここではバイトオーダーの変換を行っている
        // u16, u32 のような値を表現するのに複数バイトが必要な方は、セグメントにセットする際にビッグエンディアンに変換する必要がある
        self.buffer[0..2].copy_from_slice(&port.to_be_bytes());
    }

    pub fn set_dest(&mut self, port: u16) {
        // `port.to_be_bytes()` としている箇所は、ここではバイトオーダーの変換を行っている
        // u16, u32 のような値を表現するのに複数バイトが必要な方は、セグメントにセットする際にビッグエンディアンに変換する必要がある
        self.buffer[2..4].copy_from_slice(&port.to_be_bytes())
    }

    pub fn set_seq(&mut self, seq: u32) {
        self.buffer[4..8].copy_from_slice(&seq.to_be_bytes())
    }

    pub fn set_ack(&mut self, ack: u32) {
        self.buffer[8..12].copy_from_slice(&ack.to_be_bytes())
    }

    pub fn set_data_offset(&mut self, offset: u8) {
        self.buffer[12] |= offset << 4;
    }

    pub fn set_flag(&mut self, flag: u8) {
        self.buffer[13] = flag;
    }

    pub fn set_window_size(&mut self, window: u16) {
        self.buffer[14..16].copy_from_slice(&window.to_be_bytes())
    }

    pub fn set_checksum(&mut self, checksum: u16) {
        self.buffer[16..18].copy_from_slice(&checksum.to_be_bytes())
    }

    pub fn set_payload(&mut self, payload: &[u8]) {
        self.buffer[TCP_HEADER_SIZE..TCP_HEADER_SIZE + payload.len() as usize]
            .copy_from_slice(payload)
    }

    // ////////////////////////////////////////////////////////////////////////
    // Getters
    // ////////////////////////////////////////////////////////////////////////

    pub fn get_src(&self) -> u16 {
        // `set_src()` とは逆に、ビッグエンディアンからホストマシンのバイトオーダーに変換する必要がある
        u16::from_be_bytes([self.buffer[0], self.buffer[1]])
    }

    pub fn get_dest(&self) -> u16 {
        // `set_src()` とは逆に、ビッグエンディアンからホストマシンのバイトオーダーに変換する必要がある
        u16::from_be_bytes([self.buffer[2], self.buffer[3]])
    }

    pub fn get_seq(&self) -> u32 {
        u32::from_be_bytes([
            self.buffer[4],
            self.buffer[5],
            self.buffer[6],
            self.buffer[7],
        ])
    }

    pub fn get_ack(&self) -> u32 {
        u32::from_be_bytes([
            self.buffer[8],
            self.buffer[9],
            self.buffer[10],
            self.buffer[11],
        ])
    }

    pub fn get_flag(&self) -> u8 {
        self.buffer[13]
    }

    pub fn get_window_size(&self) -> u16 {
        u16::from_be_bytes([self.buffer[14], self.buffer[15]])
    }

    pub fn get_checksum(&self) -> u16 {
        u16::from_be_bytes([self.buffer[16], self.buffer[17]])
    }

    // ////////////////////////////////////////////////////////////////////////
    // Misc
    // ////////////////////////////////////////////////////////////////////////

    pub fn is_correct_checksum(&self, local_addr: Ipv4Addr, remote_addr: Ipv4Addr) -> bool {
        self.get_checksum()
            == util::ipv4_checksum(
                &self.packet(),
                8,
                &[],
                &local_addr,
                &remote_addr,
                IpNextHeaderProtocols::Tcp,
            )
    }
}

// 送受信の際に利用する pnet の関数がこのトレイトを実装した型を引数に要求するため
impl Packet for TcpPacket {
    fn packet(&self) -> &[u8] {
        &self.buffer
    }

    fn payload(&self) -> &[u8] {
        &self.buffer[TCP_HEADER_SIZE..]
    }
}

impl Debug for TcpPacket {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            r"
                src: {}
                dst: {}
                flag: {}
                payload_len: {}",
            self.get_src(),
            self.get_dest(),
            crate::tcpflags::flag_to_string(self.get_flag()),
            self.packet().len(),
        )
    }
}

impl From<pnet::packet::tcp::TcpPacket> for TcpPacket {
    fn from(packet: pnet::packet::tcp::TcpPacket) -> Self {
        Self {
            buffer: packet.packet().to_vec(),
        }
    }
}
