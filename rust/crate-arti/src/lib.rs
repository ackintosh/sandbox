#[cfg(test)]
mod tests {
    use arti_client::{TorClient, TorClientConfig};
    use std::error::Error;
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    // https://crates.io/crates/arti-client
    #[tokio::test]
    async fn it_works() -> Result<(), Box<dyn Error>> {
        let config = TorClientConfig::default();
        let tor_client = TorClient::create_bootstrapped(config).await?;

        let mut stream = tor_client.connect(("example.com", 80)).await?;
        stream
            .write_all(b"GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n")
            .await?;
        stream.flush().await?;

        let mut buf = vec![];
        stream.read_to_end(&mut buf).await?;

        println!("{}", String::from_utf8_lossy(&buf));

        Ok(())
    }
}
