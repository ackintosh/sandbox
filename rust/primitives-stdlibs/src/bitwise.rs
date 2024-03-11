#[test]
fn and() {
    println!("{}", 1 & 5); // 1
    println!("{}", 5 & 12); // 4
}

#[test]
fn or() {
    let a = 1;
    let b = 2;
    println!("{}", a | b); // 3
}

#[test]
fn xor() {
    // How do I print an integer in binary with leading zeros?
    // https://stackoverflow.com/questions/44690439/how-do-i-print-an-integer-in-binary-with-leading-zeros
    //
    //                          Width  0       8      16      24      32
    //                                 |       |       |       |       |
    // println!("{:#010b}", 1i8);  // 0b00000001
    // println!("{:#018b}", 1i16); // 0b0000000000000001
    // println!("{:#034b}", 1i32); // 0b00000000000000000000000000000001
    println!("{:#010b}", 1 ^ 2);
    println!("{:#010b}", 4 ^ 3);
}

#[test]
fn shift() {
    assert_eq!(1, 1 << 0);
    assert_eq!(2, 1 << 1);
    assert_eq!(4, 1 << 2);
    assert_eq!(8, 1 << 3);
}

#[test]
fn check_bits() {
    // 2ビット目がたっているかどうかチェックする
    let nums = vec![1, 2, 4, 12, 16];
    for n in nums {
        let result = (n >> 2) & 1; // 2ビット右にずらして、1との bitwise AND をとる
        println!("second bit of {n} is ... {result}");
    }
}

#[test]
fn replace() {
    // c++ - Bitwise replacing bits in two numbers - Stack Overflow
    // https://stackoverflow.com/questions/48948962/bitwise-replacing-bits-in-two-numbers

    // x
    let x: i32 = 64;
    println!("x: {:#010b}", x); // 01000000

    // y
    let y: i32 = 191;
    println!("y: {:#010b}", y); // 10111111

    // m
    let bits_to_replace: u8 = 2; // 先頭2bitを対象とする
    let m = (2_i32.pow(bits_to_replace as u32) - 1) << (8 - bits_to_replace);
    println!("m: {:#010b}", m); // 11000000

    // replaceを行う
    //   -> xの先頭2bitを、yの先頭2bitで置き換える
    let z = x ^ ((x ^ y) & m);
    println!("z: {:#010b}", z); // 10000000
}
