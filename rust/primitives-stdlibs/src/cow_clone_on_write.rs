// std::borrow::Cow
// https://doc.rust-lang.org/std/borrow/enum.Cow.html
// https://qiita.com/Kogia_sima/items/6899c5196813cf231054#%E3%81%A1%E3%82%87%E3%81%A3%E3%81%A8%E5%BE%85%E3%81%A3%E3%81%9F
// Cowとは、参照型と所有型のいずれかを保持することが出来るオブジェクト
// つまり、一つの変数でデータを参照することも、変数を所有することも出来る

use std::borrow::Cow;

// https://doc.rust-lang.org/std/borrow/enum.Cow.html#examples
#[test]
fn example1() {
    fn abs_all(input: &mut Cow<[i32]>) {
        for i in 0..input.len() {
            let v = input[i];
            if v < 0 {
                // Cow が所有していない場合は vector へ clone される
                input.to_mut()[i] = -v;
            }
        }
    }

    // cloneが発生しない
    // -> `input` が変化しないので clone が発生しない
    let slice = [1, 0, 1];
    let mut input = Cow::from(&slice[..]);
    abs_all(&mut input);
    println!("slice: {:?}", slice); // [1, 0, 1]
    println!("input: {:?}", input); // [1, 0, 1]

    // cloneが発生する
    // -> abs_all が `input` を変化させるので (sliceからvectorへ) clone が発生する.
    let slice = [-1, 0, 1];
    let mut input = Cow::from(&slice[..]);
    abs_all(&mut input);
    println!("slice: {:?}", slice); // [-1, 0, 1] -> clone が発生したので `slice` は変化しない
    println!("input: {:?}", input); // [1, 0, 1]

    // cloneが発生しない
    // -> すでに vector で、Cowが所有しているので clone が発生しない
    let mut input = Cow::from(vec![-1, 0, 1]);
    abs_all(&mut input);
    println!("input: {:?}", input); // [1, 0, 1]
}
