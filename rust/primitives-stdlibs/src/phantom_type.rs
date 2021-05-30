// https://caddi.tech/archives/1373
mod money {
    use std::marker::PhantomData;
    use std::ops::Add;

    // このケースでは通貨単位を型として表現している
    // Money<T>のTで通貨単位を表すようにする
    // ここで嬉しいのは、誤った通貨単位同士の加算をコンパイル時に検査できること
    #[derive(Debug, PartialEq)]
    struct Money<T> {
        amount: u32,
        // Tはただのラベルとして扱いたいだけだが消費しないと怒られるので、std::marker::PhantomDataを使う
        currency: PhantomData<T>,
    }

    impl<T> Money<T> {
        fn new(amount: u32) -> Self {
            Self {
                amount,
                currency: PhantomData::<T>,
            }
        }
    }

    impl<T> Add for Money<T> {
        type Output = Money<T>;

        fn add(self, other: Money<T>) -> Self::Output {
            // Phantom Typeを使わない場合、下記のように実行時にチェックしなければならない
            // if self.currency != other.currency {
            //     panic!("invalid currency")
            // }

            Self::new(self.amount + other.amount)
        }
    }

    #[derive(Debug, PartialEq)]
    enum Jpy {}
    #[derive(Debug, PartialEq)]
    enum Usd {}

    #[test]
    fn test_phantom_money() {
        let jpy1 = Money::<Jpy>::new(10);
        let jpy2 = Money::<Jpy>::new(20);

        let result = jpy1 + jpy2;
        assert_eq!(result, Money::<Jpy>::new(30));

        // *** T が異なる Money 同士ではコンパイルエラー ***
        // let jpy3 = Money::<JPY>::new(30);
        // let usd = Money::<USD>::new(10);
        // let _ = jpy3 + usd;
        // mismatched types [E0308] expected `Money<JPY>`, found `Money<USD>`
    }
}
