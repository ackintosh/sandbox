// 実際に quickcheck が使われているテストの例
// * https://github.com/sigp/discv5/blob/master/src/kbucket/bucket.rs
// * https://github.com/libp2p/rust-libp2p/blob/master/protocols/gossipsub/tests/smoke.rs

// #[macro_use]
// extern crate quickcheck;

// `#[quickcheck]` アトリビュートを使うために必要
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

fn reverse<T: Clone>(xs: &[T]) -> Vec<T> {
    let mut rev = vec![];
    for x in xs.iter() {
        rev.insert(0, x.clone());
    }
    rev
}

// exampleそのまま
// https://github.com/BurntSushi/quickcheck#simple-example
#[cfg(test)]
mod tests_example {
    use super::*;
    use quickcheck::quickcheck;

    // マクロを使うパターン
    quickcheck! {
        fn prop(xs: Vec<u32>) -> bool {
            xs == reverse(&reverse(&xs))
        }
    }

    // attributeを使うパターン
    // マクロだとIntelliJのコード追跡の対象から外れたりするので、こちらの方が良いかもしれない
    #[quickcheck]
    fn double_reversal_is_identity(xs: Vec<u32>) -> bool {
        xs == reverse(&reverse(&xs))
    }
}

// quickcheck::quickcheck() を使うパターン
mod tests {
    use super::*;
    use quickcheck::quickcheck;

    #[test]
    fn test() {
        fn prop(xs: Vec<u32>) -> bool {
            xs == reverse(&reverse(&xs))
        }

        quickcheck(prop as fn(_) -> _);
    }
}
