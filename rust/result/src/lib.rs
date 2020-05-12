// std::result::Result

///////////////////////////////////
// map_or
// https://doc.rust-lang.org/std/result/enum.Result.html#method.map_or
///////////////////////////////////
#[test]
fn result_map_or() {
    fn returns_result(v: &str) -> Result<String, String> {
        match v {
            "ok" => Ok("ok".to_owned()),
            _ => Err("error".to_owned())
        }
    }

    assert_eq!(
        "ok".to_owned(),
        returns_result("ok")
            .map_or("default".to_owned(), |s| s)
    );

    assert_eq!(
        "default".to_owned(),
        returns_result("xxx")
            .map_or("default".to_owned(), |s| s)
    );

    fn returns_another_result(n: u64) -> Result<u64, String> {
        match n {
            100 => Ok(100),
            _ => Err("error".to_owned())
        }
    }

    assert_eq!(
        true,
        returns_another_result(100)
            .map_or(false, |i| i > 1 )
    )
}