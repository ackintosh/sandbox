// # ライフタイム識別子の使い方
// 引数の全参照と、戻り値が同じライフタイム `'a` になる
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

#[test]
fn test_longest() {
    // <引数に渡す2つの文字列スライスのライフタイムが同じパターン>
    {
        let x = String::from("xxx");
        let y = String::from("y");
        let result = longest(x.as_str(), y.as_str());

        assert_eq!(result, x);
    }

    // <引数に渡す2つの文字列スライスのライフタイムが "異なる" パターン>
    // * ライフタイムが異なるが、longest関数のシグニチャで指定しているライフタイム 'a は満たしているのでコンパイルできる
    //   -> longest関数は `x` への参照を返す
    // * ただし、返り値のスコープは「2つの引数の小さい方のライフタイムになる」
    {
        let x = String::from("xxx");
        let result;
        {
            let y = String::from("y"); // yのスコープの方が短い
            // ライフタイムに問題無いので実行できる
            result = longest(x.as_str(), y.as_str());
            assert_eq!(result, x);
        }

        // 返り値 `result` の値は "xxx" だが、スコープは短い方( = yのスコープ)になるので、
        // yのスコープを抜けたあとで `result` を使うことはできない
        // println!("result: {}", result);
        // <コンパイルエラー>
        //   -> error[E0597]: `y` does not live long enough
    }
}

// # 引数の参照に 必ずしもライフタイム識別子が必要なわけではない
// * 第2引数 `y` にはライフタイム識別子を指定していない
// * `y` のライフタイムは `x` や戻り値に関係無いので 指定する必要が無い
fn longest_without_lifetime<'a>(x:&'a str, _y: &str) -> &'a str {
    // コンパイル出来る
    x // 必ず `x` を返す
}

#[test]
fn test_longest_without_lifetime() {
    let x = String::from("xxx");
    let y = String::from("y");
    let result = longest_without_lifetime(x.as_str(), y.as_str());

    assert_eq!(result, x);
}

// # 構造体定義のライフタイム注釈
// Excerptのインスタンスが、 `part` フィールドに保持している参照よりも短命であることを意味する
struct Excerpt<'a> {
    part: &'a str,
}

#[test]
fn test_excerpt() {
    // `novel`データは、Excerptインスタンスを生成する前に存在している
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.')
        .next()
        .expect("Should have a '.'");

    // excerptがスコープを抜けるまでは `novel` はスコープを抜けないので、excerptインスタンスは有効
    let _excerpt = Excerpt { part: first_sentence };
}
