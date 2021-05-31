// メモ
// https://scrapbox.io/bring-me-the-horizon/Rust_:_dyn%EF%BC%88%E5%8B%95%E7%9A%84%E3%83%87%E3%82%A3%E3%82%B9%E3%83%91%E3%83%83%E3%83%81%E3%81%A8%E9%9D%99%E7%9A%84%E3%83%87%E3%82%A3%E3%82%B9%E3%83%91%E3%83%83%E3%83%81%EF%BC%89

trait Tweet {
    fn tweet(&self);
}

struct Dove;
struct Duck;

impl Tweet for Dove {
    fn tweet(&self) {
        println!("Coo!");
    }
}

impl Tweet for Duck {
    fn tweet(&self) {
        println!("Quack!");
    }
}

/////////////////////////////////////////
// 静的ディスパッチの例
/////////////////////////////////////////
#[test]
fn static_dispatch() {
    let bird = Dove {};
    // Dove::tweet を実行すべきと明らかなので、コンパイル時に解決する( = 静的ディスパッチ)
    bird.tweet(); // Coo!
}

/////////////////////////////////////////
// 動的ディスパッチの例
/////////////////////////////////////////
#[test]
fn dynamic_dispatch() {
    let dove = Dove;
    let duck = Duck;

    // DoveとDuckそれぞれのインスタンスを、Vec<Box<dyn Tweet>>型に収めている.
    // 2つの型が共通のトレイトを持っていることで、どちらも Box<dyn Tweet> というように画一的にポインタとして扱うことができている
    let birds: Vec<Box<dyn Tweet>> = vec![Box::new(dove), Box::new(duck)];

    for bird in birds {
        // どちらのインスタンスが実行したメソッドなのか、アプリケーションを動かしてみるまでわからないので
        // 静的ディスパッチでは解決できない.
        // `dyn` を使って、トレイトオブジェクトへの動的ディスパッチを行うことで実現する.
        bird.tweet();
    }
    // Coo!
    // Quack!
}
