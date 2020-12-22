#[test]
fn test_loop() {
    let mut i = 0;
    loop {
        i += 1;

        if i % 2 == 0 {
            continue;
        }
        if i > 10 {
            break;
        }

        println!("{}", i);
    }
    // 1
    // 3
    // 5
    // 7
    // 9
}
