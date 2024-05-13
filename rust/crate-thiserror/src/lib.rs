// https://docs.rs/thiserror/latest/thiserror/

// * std::error::Errorトレイトを実装するderiveマクロを提供しているので、手書きする手間を省ける

#[cfg(test)]
mod tests {

    #[derive(thiserror::Error, Debug)]
    enum DataStoreError {
        #[error("data store disconnected")] // `#[error("...")` でDisplayトレイトを実装する
        Disconnect(#[from] std::io::Error), // Fromトレイトを実装する
    }

    #[test]
    fn it_works() {
        let connect = || -> Result<(), std::io::Error> {
            Err(std::io::Error::from(std::io::ErrorKind::ConnectionAborted))
        };

        let send_rpc_request = || -> Result<(), DataStoreError> {
            connect()?; // `DataStoreError::Disconnect`がFromトレイトを実装しているので変換される
            Ok(())
        };

        let result = send_rpc_request();

        println!("{:?}", result);
        // Err(Disconnect(Kind(ConnectionAborted)))

        println!("{}", result.unwrap_err().to_string());
        // data store disconnected
    }
}
