#[test]
fn unwrap_or_else() {
    let f = || Some(1);
    assert_eq!(1, f().unwrap());

    let f = || None;
    assert_eq!(9, f().unwrap_or(9));

    let f: fn() -> Result<u32, String> = || Ok(1);
    assert_eq!(1, f().unwrap());

    let f: fn() -> Result<u32, String> = || Err("error".to_owned());
    assert_eq!(
        9,
        f().unwrap_or_else(|e| {
            // Result型の場合は引数を取れる
            println!("{}", e); // error

            9
        })
    );

    let f: fn() -> Result<u32, String> = || Err("error".to_owned());

    let result = f().map(|r| r == 100).unwrap_or_else(|e| {
        println!("{}", e); // error
        false
    });
    assert!(!result);
}

///////////////////////////////////
// map_or
// https://doc.rust-lang.org/std/result/enum.Result.html#method.map_or
///////////////////////////////////
#[test]
fn result_map_or() {
    fn returns_result(v: &str) -> Result<String, String> {
        match v {
            "ok" => Ok("ok".to_owned()),
            _ => Err("error".to_owned()),
        }
    }

    assert_eq!(
        "ok".to_owned(),
        returns_result("ok").map_or("default".to_owned(), |s| s)
    );

    assert_eq!(
        "default".to_owned(),
        returns_result("xxx").map_or("default".to_owned(), |s| s)
    );

    fn returns_another_result(n: u64) -> Result<u64, String> {
        match n {
            100 => Ok(100),
            _ => Err("error".to_owned()),
        }
    }

    assert!(returns_another_result(100).map_or(false, |i| i > 1));
}
