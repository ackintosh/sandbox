#[cfg(test)]
mod tests {
    use chrono::prelude::*;

    #[test]
    fn it_works() {
        let local = Local::now();

        println!("{}", local);
        // 2020-12-12 07:01:46.005411 +09:00
    }

    #[test]
    fn parse() {
        // https://rust-lang-nursery.github.io/rust-cookbook/datetime/parse.html#parse-string-into-datetime-struct
        let no_timezone =
            NaiveDateTime::parse_from_str("2015-09-05 23:56:04", "%Y-%m-%d %H:%M:%S").unwrap();
        println!("{:?}", no_timezone);
        // Ok(2015-09-05T23:56:04)
    }
}
