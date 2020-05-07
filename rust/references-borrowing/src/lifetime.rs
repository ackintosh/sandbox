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