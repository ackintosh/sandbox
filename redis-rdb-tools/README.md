https://github.com/sripathikrishnan/redis-rdb-tools


Dockerhub redis https://hub.docker.com/_/redis


## Redisサーバの起動

```bash
# --save 10 1
# → 10秒ごとにrdbファイルを書き込む(1回以上の書き込みオペレーションがあれば

# Redisのバージョンは 6 (6-bullseye) を指定している
# → 7以上だと、RDBファイルのバージョンが10になり
#    redis-rdb-tools が RDBバージョン10 に対応していないので、
#    `Exception: ('verify_version', 'Invalid RDB version number 10')` というエラーが出てしまう.
#    https://github.com/sripathikrishnan/redis-rdb-tools/issues/185

docker run -v $PWD:/data --rm -it -p 6379:6379 redis:6-bullseye redis-server --save 10 1
```

## redis-cli

```bash
# 適当なTTL付きのデータを入れる
$ redis-cli
127.0.0.1:6379> SET testkey hello EX 1000
OK
127.0.0.1:6379> TTL testkey
(integer) 994
127.0.0.1:6379> save
OK
```

## redis-rdb-tools

#### rdbファイルからexpireを除外してインポートする

参考: https://github.com/sripathikrishnan/redis-rdb-tools#emitting-redis-protocol

```bash
# rdbファイルが作られていることを確認
$ ls dump.rdb

# expireありで出力する
$ rdb -c protocol ./dump.rdb
*2
$6
SELECT
$1
0
*3
$3
SET
$7
testkey
$5
hello
*3
$8
EXPIREAT
$7
testkey
$10
1675552879

# exire無しで出力する
$ rdb --no-expire -c protocol ./dump.rdb
*2
$6
SELECT
$1
0
*3
$3
SET
$7
testkey
$5
hello

# Redisサーバを起動しなおしてデータを空にする
# → -v や --save を指定せずに起動する
$ docker run --rm -it -p 6379:6379 redis:6-bullseye redis-server
## 確認
127.0.0.1:6379> GET testkey
(nil)


# Redisにexpire無しでインポートする
$ rdb --no-expire -c protocol ./dump.rdb | redis-cli --pipe
All data transferred. Waiting for the last reply...
Last reply received from server.
errors: 0, replies: 2
## インポート後、ttlが消えたことを確認
127.0.0.1:6379> GET testkey
"hello"
127.0.0.1:6379> TTL testkey
(integer) -1
```




