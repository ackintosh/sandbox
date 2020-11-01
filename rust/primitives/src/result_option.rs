#[test]
fn unwrap_or_else() {
    let f = || { Some(1) };
    assert_eq!(1, f().unwrap());

    let f = || { None };
    assert_eq!(9, f().unwrap_or_else(|| 9));

    let f: fn() -> Result<u32, String> = || { Ok(1) };
    assert_eq!(1, f().unwrap());

    let f: fn() -> Result<u32, String> = || { Err("error".to_owned()) };
    assert_eq!(9, f().unwrap_or_else(|e| { // Result型の場合は引数を取れる
        println!("{}", e); // error

        9
    }));

    let f: fn() -> Result<u32, String> = || { Err("error".to_owned()) };

    let result = f()
        .map(|r| {r == 100 })
        .unwrap_or_else(|e| {
            println!("{}", e); // error
            false
        });
    assert!(!result);

}
