// 参考
// Rustの非同期プログラミングをマスターする - OPTiM TECH BLOG
// https://tech-blog.optim.co.jp/entry/2019/11/08/163000

use std::time::Duration;

#[async_std::main]
async fn main() {
    // async_std バージョンの sleep
    async_std::task::sleep(Duration::from_secs(1)).await;

    println!("Hello, world!");
}
