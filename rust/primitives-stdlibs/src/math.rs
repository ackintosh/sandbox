#[test]
fn test() {
    let n = 4i32 / 2i32;
    assert_eq!(n, 2);

    // i32 として扱われる
    let n = 3 / 2;
    // 小数点以下が切り捨てられる
    assert_eq!(n, 1);

    let n = 3f32 / 2f32;

    ///////////////////////////////
    // 浮動小数点の比較
    // https://rust-lang.github.io/rust-clippy/master/index.html#float_cmp
    ///////////////////////////////

    let x = 1.2331f64;
    let y = 1.2332f64;
    let yy = 1.2331f64;

    if y == x {
        println!("1. ============");
    } else {
        println!("1. !!!!!!!!!!!!");
    }
    if yy == x {
        println!("2. ============");
    } else {
        println!("2. !!!!!!!!!!!!");
    }

    let diff = (x - y).abs();
    println!("diff: {:?}", diff);

    if diff == f64::EPSILON {
        println!("======f64::EPSILON");
    }
    if diff < f64::EPSILON {
        println!("<<<<<<f64::EPSILON");
    } else {
        println!(">>>>>>f64::EPSILON");
    }

    // 浮動小数点の計算の不正確さを許容するために f32::EPSILON を使う
    let error_margin = f32::EPSILON;
    assert!((n - 1.5f32).abs() < error_margin);

    println!("{:?}", n);
}

mod ordering {
    #[test]
    fn test() {
        assert_eq!(7, 2 * 3 + 1);
        assert_eq!(7, 1 + 2 * 3);
    }
}

mod overflow {
    use std::ops::Add;

    #[test]
    fn saturating() {
        let n = 10u8;
        assert_eq!(255, n.add(245));

        // u8 の上限を超えるのでオーバーフローが起きてしまう
        //
        // エラーメッセージ:
        // attempt to add with overflow
        // thread 'math::saturating' panicked at 'attempt to add with overflow'
        // let _ = n.add(246);

        // saturating_add を使えば、上限で止まって、エラーにならない
        let result = n.saturating_add(246);
        assert_eq!(255, result);
    }
}

mod underflow {
    #[test]
    fn saturating_sub() {
        let ten = 10u32;

        // let result = ten - 11;
        // *下記エラーになる*
        // =======================================================================
        // attempt to subtract with overflow
        // thread 'underflow' panicked at 'attempt to subtract with overflow',
        // =======================================================================

        // saturating_sub を使うことでunderflowを防げる
        // https://doc.rust-lang.org/std/primitive.usize.html#method.saturating_sub
        assert_eq!(ten.saturating_sub(11), 0);
    }

    #[test]
    fn checked_sub() {
        assert_eq!(10u32.checked_sub(1), Some(9));
        assert_eq!(10u32.checked_sub(100), None);
    }
}
