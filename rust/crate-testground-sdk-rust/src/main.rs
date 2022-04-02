use std::time::Duration;
use rand::Rng;

#[async_std::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Sync serviceと通信するためのクライアント
    let mut sync_client = testground::sync::Client::new().await?;

    // ランダムな時間 sleep する
    let mut rng = rand::thread_rng();
    let uniform = rand::distributions::Uniform::new(1, 10);
    async_std::task::sleep(Duration::from_secs(rng.sample(uniform))).await;

    let state = "ready".to_string();

    // ready の状態になったことを通知する
    sync_client.signal(state.clone()).await?;

    // 参加ノードすべてが ready の状態になるまで待つ
    sync_client.wait_for_barrier(state, 2).await?;

    sync_client.publish_success().await?;

    Ok(())
}
