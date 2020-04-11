use std::net::TcpStream;
use std::io::{Write, BufReader, BufRead};

pub fn connect(address: &str) -> Result<(), failure::Error> {
    let mut stream = TcpStream::connect(address)?;

    loop {
        let mut input = String::new();
        std::io::stdin().read_line(&mut input)?;
        stream.write_all(input.as_bytes())?;

        let mut reader = BufReader::new(&stream);
        let mut buffer = Vec::new();
        reader.read_until(b'\n', &mut buffer)?;
        print!("{}", std::str::from_utf8(&buffer)?);
    }
}