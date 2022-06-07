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
    // マクロだとIntelliJのコード追跡の対象から外れたりするので、こちらや、後述の quickcheck::quickcheck() を使うパターンの方が良さそう
    #[quickcheck]
    fn double_reversal_is_identity(xs: Vec<u32>) -> bool {
        xs == reverse(&reverse(&xs))
    }
}

#[derive(Clone, Debug)]
struct Person {
    age: u8,
}

mod tests {
    use super::*;
    use quickcheck::quickcheck;

    // quickcheck::quickcheck() を使うパターン
    #[test]
    fn test() {
        fn prop(xs: Vec<u32>) -> bool {
            xs == reverse(&reverse(&xs))
        }

        quickcheck(prop as fn(_) -> _);
    }

    // テスト用モジュールの中で Arbitrary トレイトを実装するパターン
    mod property_based_tests {
        use crate::Person;
        use quickcheck::{Arbitrary, Gen};

        impl Arbitrary for Person {
            fn arbitrary(g: &mut Gen) -> Self {
                Person {
                    age: u8::arbitrary(g),
                }
            }
        }

        #[quickcheck]
        fn person(person: Person) {
            println!("person: {:?}", person);
        }
    }
}

mod arbitrary_structs {
    use quickcheck::{Arbitrary, Gen};

    #[derive(Clone, Debug)]
    enum Status {
        Connected,
        Disconnected,
    }

    // ref: https://github.com/BurntSushi/quickcheck#generating-structs
    impl Arbitrary for Status {
        fn arbitrary(g: &mut Gen) -> Self {
            g.choose(&[Status::Connected, Status::Disconnected])
                .unwrap()
                .clone()
        }
    }

    #[derive(Clone, Debug)]
    enum Direction {
        Outgoing,
        Incoming,
    }

    impl Arbitrary for Direction {
        fn arbitrary(g: &mut Gen) -> Self {
            g.choose(&[Direction::Outgoing, Direction::Incoming])
                .unwrap()
                .clone()
        }
    }

    #[derive(Clone, Debug)]
    struct Node {
        status: Status,
        direction: Direction,
    }

    impl Arbitrary for Node {
        fn arbitrary(g: &mut Gen) -> Self {
            Node {
                status: Status::arbitrary(g),
                direction: Direction::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn test_structs(nodes: Vec<Node>) {
        println!("nodes: {:?}", nodes);
    }
}
