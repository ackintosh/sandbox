#[test]
fn underflow() {
    let ten = 10u32;

    // let result = ten - 11;
    // *下記エラーになる*
    // =======================================================================
    // attempt to subtract with overflow
    // thread 'underflow' panicked at 'attempt to subtract with overflow',
    // =======================================================================

    // saturating_sub を使うことでunderflowを防げる
    // https://doc.rust-lang.org/std/primitive.usize.html#method.saturating_sub
    assert_eq!(
        ten.saturating_sub(11),
        0
    );
}