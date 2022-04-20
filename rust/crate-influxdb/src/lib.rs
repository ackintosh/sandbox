// https://github.com/influxdb-rs/influxdb-rust

#[cfg(test)]
mod tests {
    use chrono::{DateTime, Utc};
    use influxdb::{Client, Timestamp, InfluxDbWriteable, ReadQuery};

    #[derive(InfluxDbWriteable)]
    struct WeatherReading {
        time: DateTime<Utc>,
        humidity: i32,
        #[influxdb(tag)] wind_direction: String,
    }

    // https://github.com/influxdb-rs/influxdb-rust#quickstart
    // #[test] // CIでInfluxDBを用意していないのでとりあえずコメントアウトしておく
    fn it_works() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async move {
            // 関連: sandbox/influxdb で InfluxDB を起動しておく
            let client = Client::new("http://localhost:18086", "sandbox");

            let weather_reading = WeatherReading {
                time: Timestamp::Hours(1).into(),
                humidity: 30,
                wind_direction: String::from("north"),
            };

            let write_result = client.query(weather_reading.into_query("weather")).await.unwrap();
            println!("{}", write_result);

            let read_query = ReadQuery::new("select * from weather");
            let read_result = client.query(read_query).await.unwrap();
            println!("{}", read_result);
        });
    }
}
