#[cfg(test)]
mod tests {
    use chrono::prelude::*;

    #[test]
    fn it_works() {
        let local = Local::now();

        println!("{}", local);
        // 2020-12-12 07:01:46.005411 +09:00
    }
}
