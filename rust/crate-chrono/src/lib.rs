#[cfg(test)]
mod tests {
    use chrono::prelude::*;

    #[test]
    fn it_works() {
        let local = Local::now();

        println!("{}", local);
        // 2020-12-12 07:01:46.005411 +09:00

        let utc = Utc::now();
        println!("{}", utc);
        let utc_string = utc.to_rfc3339();
        println!("{}", utc_string);
        let dt = DateTime::parse_from_rfc3339(&utc_string).unwrap();
        println!("{}", dt);
    }

    #[test]
    fn parse() {
        // ////////////////////////////
        // https://rust-lang-nursery.github.io/rust-cookbook/datetime/parse.html#parse-string-into-datetime-struct
        // ////////////////////////////

        let no_timezone =
            NaiveDateTime::parse_from_str("2015-09-05 23:56:04", "%Y-%m-%d %H:%M:%S").unwrap();
        println!("{:?}", no_timezone);
        // Ok(2015-09-05T23:56:04)

        let rfc3339 = DateTime::parse_from_rfc3339("1996-12-19T16:39:57-08:00").unwrap();
        println!("{:?}", rfc3339);
        let rfc3339 = DateTime::parse_from_rfc3339("2022-10-06T08:02:34+09:00").unwrap();
        println!("{:?}", rfc3339);
    }
}
