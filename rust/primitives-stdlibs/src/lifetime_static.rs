// Rustの2種類の 'static | 俺とお前とlaysakura
// https://laysakura.github.io/2020/05/21/rust-static-lifetime-and-static-bounds/

// /////////////////////////////
// 'static ライフタイム境界
// /////////////////////////////
// ref: https://laysakura.github.io/2020/05/21/rust-static-lifetime-and-static-bounds/#39-static-%E3%83%A9%E3%82%A4%E3%83%95%E3%82%BF%E3%82%A4%E3%83%A0-%E5%A2%83%E7%95%8C
mod static_lifetime_bounds {
    // 型に対してライフタイム境界を指定することもできる
    // 例: `T: 'static`
    //   -> T に対して 'static ライフタイム境界がついている

    // *** ポイント ***
    // 「型 T に 'staic ライフタイム境界がついているならば、T には参照を含まないことを要請する」
    //    (T が struct, enum, vector などであった場合にはその中身も参照ではないことを要請する)

    // *** 厳密には ***
    // `T: 'static` ならば、下記のいずれかになる。
    // 1. T がスカラ型の値である。（e.g. T <- 123）
    // 2. T が複合型 (struct, enum, ベクタ, 配列 など、アクセスできる内部構造を持つ型) の値であり、その内部構造は参照を持たない。
    //    (e.g. T <- struct S(u32), enum E { V1(u32), V2(i32) }, T <- Vec<u32>)
    // 3. T が複合型の値であり、その内部構造に 'static ライフタイムの参照を含む。
    //    (e.g. T <- struct S(u32, &'static u32), T <- Vec<&'static str>)
    // 4. T が、上記のいずれか値の 'static ライフタイムの参照である。
    //    (e.g. T <- &'static 123, T <- &'static S(u32))
}

// /////////////////////////////
// 'static ではないライフタイム境界
// /////////////////////////////
// -> lifetime_bounds.rsを参照
