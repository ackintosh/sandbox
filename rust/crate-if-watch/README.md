
### 検証方法(Docker)

起動済みコンテナのIPアドレスを変更する。

参考: [備忘録: 【Docker 20.10.17】起動済みのコンテナのIPアドレスを変更する方法について](https://akira-arets.blogspot.com/2022/08/linux-docker-change-ip-address-of-created-container.html)

```bash
# 検証用のnetworkを作成
# ※subnetを指定して作成しないと、IPアドレスが変更できない
#   -> subnetを指定しないと、IPアドレスを変更しようとしたときに下記のエラーメッセージが出る
#   -> user specified IP address is supported only when connecting to networks with user configured subnets
docker network create --subnet 192.168.0.0/24 iftest

# コンテナを起動してexampleを走らせておく
cd /Users/akihito/src/github.com/ackintosh/if-watch
docker run --rm -it -v ./:/tmp --net iftest --name iftestcontainer rust bash
cd /tmp
cargo run --example if_watch --features="smol"

# 起動したコンテナのIPアドレスを変更する
docker network disconnect iftest iftestcontainer # コンテナ(iftestcontainer)を、ネットワーク(iftest)から切断する
docker network connect --ip 192.168.0.20 iftest iftestcontainer # コンテナ(iftestcontainer)を、ネットワーク(iftest)に `192.168.0.20` で接続する
```

