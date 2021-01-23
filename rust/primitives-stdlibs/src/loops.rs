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

#[test]
fn test_enumerate() {
    for (i, s) in vec![1, 2, 3].iter().enumerate() {
        println!("i: {}, s: {}", i, s);
        // i: 0, s: 1
        // i: 1, s: 2
        // i: 2, s: 3
    }
}
