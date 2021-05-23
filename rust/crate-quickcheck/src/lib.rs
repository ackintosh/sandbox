#[macro_use]
extern crate quickcheck;

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

    quickcheck! {
        fn prop(xs: Vec<u32>) -> bool {
            xs == reverse(&reverse(&xs))
        }
    }
}

// マクロではなく quickcheck::quickcheck() を使うパターン
// マクロだとIntelliJのコード追跡の対象から外れたりするので、こちらの方が良いかもしれない
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
