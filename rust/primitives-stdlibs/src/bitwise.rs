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
    let x: u8 = 64; // 01000000
    println!("x: {:#010b}", x);

    // y
    let y: u8 = 191; // 10111111
    println!("y: {:#010b}", y);

    // m
    let m: u8 = 3 << 6; // 11000000 -> 先頭2bitをreplaceの対象とする
    println!("m: {:#010b}", m);

    // replaceを行う
    //   -> xの先頭2bitを、yの先頭2bitで置き換える
    let z = x ^ ((x ^ y) & m); // 10000000
    println!("z: {:#010b}", z);
}
