use pnet::packet::Packet;

const TCP_HEADER_SIZE: usize = 20;

#[derive(Clone)]
pub struct TcpPacket {
    buffer: Vec<u8>,
}

impl TcpPacket {
    pub fn new(payload_len: usize) -> Self {
        Self {
            buffer: vec![0; TCP_HEADER_SIZE + payload_len],
        }
    }

    pub fn set_src(&mut self, port: u16) {
        // `port.to_be_bytes()` としている箇所は、ここではバイトオーダーの変換を行っている
        // u16, u32 のような値を表現するのに複数バイトが必要な方は、セグメントにセットする際にビッグエンディアンに変換する必要がある
        self.buffer[0..2].copy_from_slice(&port.to_be_bytes());
    }

    pub fn set_dest(&mut self, port: u16) {
        self.buffer[2..4].copy_from_slice(&port.to_be_bytes())
    }

    pub fn set_flag(&mut self, flag: u8) {
        self.buffer[13] = flag;
    }
}

// 送受信の際に利用する pnet の関数がこのトレイとを実装した型を引数に要求するため
impl Packet for TcpPacket {
    fn packet(&self) -> &[u8] {
        &self.buffer
    }

    fn payload(&self) -> &[u8] {
        &self.buffer[TCP_HEADER_SIZE..]
    }
}
