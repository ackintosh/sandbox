use uint::construct_uint;

construct_uint! {
    // 4 x 64bit -> 256bits
    pub struct U256(4);
}

// 使い方
// ref: https://github.com/paritytech/parity-common/blob/master/uint/tests/uint_tests.rs

#[test]
fn test() {
    let uint = U256::from(100u64);
    println!("{}", uint); // 100

    // u128::max_value()
    //   -> 340282366920938463463374607431768211455
    let uint = U256::from(u128::max_value());

    let r = uint.checked_add(U256::from(10u32));

    // +10された数値
    // 340282366920938463463374607431768211465
    println!("{:?}", r.unwrap());

    // uintは変わらない
    // 340282366920938463463374607431768211455
    println!("{:?}", uint);
}

#[test]
fn xor() {
    let a = U256::from(4u64); // 100
    let b = U256::from(5u64); // 101
    println!("{}", a ^ b); // XOR
                           // 1 (001)

    let a = U256::from(3u64); // 0011
    let b = U256::from(12u64); // 1100
    println!("{}", a ^ b); // XOR
                           // 15(1111)
}
