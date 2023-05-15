// ///////////////////
// ライフタイム境界
// ///////////////////

// Trait and lifetime bounds - The Rust Reference
// https://doc.rust-lang.org/reference/trait-bounds.html)

// Rustの2種類の 'static | 俺とお前とlaysakura
// https://laysakura.github.io/2020/05/21/rust-static-lifetime-and-static-bounds/

// /////////////////////////////
// 'static ライフタイム境界
// /////////////////////////////
// ref: https://laysakura.github.io/2020/05/21/rust-static-lifetime-and-static-bounds/#39-static-%E3%83%A9%E3%82%A4%E3%83%95%E3%82%BF%E3%82%A4%E3%83%A0-%E5%A2%83%E7%95%8C
// -> lifetime_static.rsを参照

// /////////////////////////////
// 'static ではないライフタイム境界
// /////////////////////////////
// ref: https://laysakura.github.io/2020/05/21/rust-static-lifetime-and-static-bounds/#%E3%81%8A%E3%81%BE%E3%81%91-39-static-%E3%81%98%E3%82%83%E3%81%AA%E3%81%84%E3%83%A9%E3%82%A4%E3%83%95%E3%82%BF%E3%82%A4%E3%83%A0%E5%A2%83%E7%95%8C
mod non_static_lifetime_bounds {
    // 例: `T: 'a`
    //
    // この場合も 'static ライフタイムと同様、
    // 「T （自体やそのフィールド）には参照が含まれていない。または参照が含まれていたら、その参照のライフタイムは全て 'a 以上」
    // という制約を表す。
}
