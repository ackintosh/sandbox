// 下記の件を、ミニマムのコードで理解する
// https://github.com/ackintosh/rust-libp2p/pull/55

mod prometheus {
    pub trait Text {}

    pub trait Proto {}

    pub struct Registry<M = Box<dyn Text>> {
        pub metrics: Vec<M>,
    }

    impl<M> Registry<M> {
        pub fn register(&mut self, metric: M) {
            self.metrics.push(metric);
        }
    }

    #[derive(Clone, Debug)]
    pub struct Family {}

    impl Text for Family {}
    impl Proto for Family {}
}

// ////////////////////////////////////////////////////////////////////////////
// 改修前
//
// Registryの型パラメータのデフォルトが `Box<dyn Text>` に指定されていて、
// それでコンパイルされる。
// ////////////////////////////////////////////////////////////////////////////
mod before {
    use crate::generics_gossipsub::prometheus;
    use crate::generics_gossipsub::prometheus::{Family, Registry};

    #[derive(Debug)]
    pub struct Gossipsub {
        #[allow(dead_code)]
        metrics: Metrics,
    }

    impl Gossipsub {
        pub fn new_with_metrics(registry: &mut Registry) -> Self {
            let metrics = Metrics::new(registry);

            Self { metrics }
        }
    }

    #[derive(Debug)]
    struct Metrics {
        #[allow(dead_code)]
        family: prometheus::Family,
    }

    impl Metrics {
        fn new(registry: &mut Registry) -> Self {
            let family = Family {};

            registry.register(Box::new(family.clone()));

            Self { family }
        }
    }

    #[test]
    fn test() {
        let mut registry = Registry { metrics: vec![] };

        let gossipsub = Gossipsub::new_with_metrics(&mut registry);
        println!("{:?}", gossipsub);
    }
}

// ////////////////////////////////////////////////////////////////////////////
// 失敗パターン (コンパイルエラーになるので、コードはコメントアウトしている)
//
// 1. Gossipsub::new_with_metrics() の引数の Registry の型パラメータを E にする (`Registry<E>`)
// 2. すると、Gossipsub::new_with_metrics() で呼び出している Metrics::new() の引数も `Registry<E>` にして整合をとる必要がある
//
// 下記のコンパイルエラーになる。
//
// error[E0308]: mismatched types
//    --> primitives-stdlibs/src/generics_gossipsub.rs:104:31
//     |
// 101 |         fn new<E>(registry: &mut Registry<E>) -> Self {
//     |                - this type parameter
// ...
// 104 |             registry.register(Box::new(family.clone()));
//     |                      -------- ^^^^^^^^^^^^^^^^^^^^^^^^ expected type parameter `E`, found struct `Box`
//     |                      |
//     |                      arguments to this function are incorrect
//     |
//     = note: expected type parameter `E`
//                        found struct `Box<Family>`
// note: associated function defined here
//    --> primitives-stdlibs/src/generics_gossipsub.rs:14:16
//     |
// 14  |         pub fn register(&mut self, metric: M) {
//     |                ^^^^^^^^ ---------  ---------
// ////////////////////////////////////////////////////////////////////////////
// mod xxx {
//     use crate::generics_gossipsub::prometheus;
//     use crate::generics_gossipsub::prometheus::{Family, Registry};
//
//     #[derive(Debug)]
//     pub struct Gossipsub {
//         metrics: Metrics,
//     }
//
//     impl Gossipsub {
//         // 1. Registry<E> にしている
//         pub fn new_with_metrics<E>(registry: &mut Registry<E>) -> Self {
//             let metrics = Metrics::new(registry);
//
//             Self { metrics }
//         }
//     }
//
//     #[derive(Debug)]
//     struct Metrics {
//         family: prometheus::Family,
//     }
//
//     impl Metrics {
//         // 2. Registry<E> にしている
//         fn new<E>(registry: &mut Registry<E>) -> Self {
//             let family = Family {};
//
//             registry.register(Box::new(family.clone()));
//
//             Self { family }
//         }
//     }
//
//     #[test]
//     fn test() {
//         let mut registry = Registry { metrics: vec![] };
//
//         let gossipsub = Gossipsub::new_with_metrics(&mut registry);
//         println!("{:?}", gossipsub);
//     }
// }

// ////////////////////////////////////////////////////////////////////////////
// Divaによる解決パターン
//
// *** 構造体への変更 ***
// * `AnyEncoder` トレイトをを追加
//   * `AnyEncoder` は Metrics オブジェクトを作る役割を持つ（ AnyEncoder::new_metrics() ）
//   * TextEncoder と ProtoEncoder は `AnyEncoder` を実装する
//   * 補足: TextEncoder と ProtoEncoder は、 prometheus::{Text, Proto} のエイリアス
// * Gossipsub の 型パラメータに <E> を追加
//   * AnyEncoder トレイトを実装していることを要求する
// * Metrics の 型パラメータに <E> を追加
//   * AnyEncoder トレイトを実装していることを要求する
//   * Metrics のフィールドに <E> は必要ないので、PhantomData<E> を使用する
//
// *** main プログラムからの流れ ***
// 1. Registry<ProtoEncoder> (または <TextEncoder>)で作る
// 2. Gossipsub::new_with_metrics()
//   * E (AnyEncoder) の new_metrics() を呼び出す
//     * -> ProtoEncoderのAnyEncoder実装が呼び出される
//     * -> Metrics<ProtoEncoder> が返る
// ////////////////////////////////////////////////////////////////////////////
mod diva {
    use crate::generics_gossipsub::prometheus;
    use crate::generics_gossipsub::prometheus::{Family, Registry};
    use std::marker::PhantomData;

    type TextEncoder = Box<dyn prometheus::Text>;
    type ProtoEncoder = Box<dyn prometheus::Proto>;

    // `Sized` が無いと下記のコンパイルエラーになる
    //
    // error[E0277]: the size for values of type `Self` cannot be known at compilation time
    //    --> primitives-stdlibs/src/generics_gossipsub.rs:154:52
    //     |
    // 154 |         fn new_metrics(registry: &mut Registry) -> Metrics<Self>;
    //     |                                                    ^^^^^^^^^^^^^ doesn't have a size known at compile-time
    //     |
    // note: required by a bound in `diva::Metrics`
    //    --> primitives-stdlibs/src/generics_gossipsub.rs:194:20
    //     |
    // 194 |     struct Metrics<E: AnyEncoder> {
    //     |                    ^ required by this bound in `diva::Metrics`
    pub trait AnyEncoder: Sized {
        fn new_metrics(registry: &mut Registry<Self>) -> Metrics<Self>;
    }

    impl AnyEncoder for TextEncoder {
        fn new_metrics(registry: &mut Registry<Self>) -> Metrics<Self> {
            let family = Family {};

            registry.register(Box::new(family.clone()));

            Metrics {
                family,
                _phantom_encoder: Default::default(),
            }
        }
    }

    impl AnyEncoder for ProtoEncoder {
        fn new_metrics(registry: &mut Registry<Self>) -> Metrics<Self> {
            let family = Family {};

            registry.register(Box::new(family.clone()));

            Metrics {
                family,
                _phantom_encoder: Default::default(),
            }
        }
    }

    #[derive(Debug)]
    pub struct Gossipsub<E: AnyEncoder> {
        metrics: Metrics<E>,
    }

    impl<E> Gossipsub<E>
    where
        E: AnyEncoder,
    {
        pub fn new_with_metrics(registry: &mut Registry<E>) -> Self {
            let metrics = E::new_metrics(registry);

            Self { metrics }
        }
    }

    #[derive(Debug)]
    pub struct Metrics<E: AnyEncoder> {
        pub family: prometheus::Family,
        _phantom_encoder: PhantomData<E>,
    }

    impl<E> Metrics<E>
    where
        E: AnyEncoder,
    {
        // ///////////////////////////////////////////////////////////
        // Metrics::new() は不要になる
        //   -> AnyEncoder::new_metrics() があるので
        // ///////////////////////////////////////////////////////////
        // fn new<E>(registry: &mut Registry<E>) -> Self {
        //     let family = Family {};
        //
        //     registry.register(Box::new(family.clone()));
        //
        //     Self { family }
        // }
    }

    #[test]
    fn test() {
        let mut registry: Registry<ProtoEncoder> = Registry { metrics: vec![] };

        let gossipsub = Gossipsub::new_with_metrics(&mut registry);
        println!("{:?}", gossipsub.metrics.family);
    }
}
