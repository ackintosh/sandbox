# InfluxDB 1.8

## 起動

```shell
$ docker-compose up
```

## CLIクライアント

```shell
# サーバに接続
$ docker-compose exec influxdb-v1 bash

# CLIクライアントを起動
$ influx
Connected to http://localhost:8086 version 1.8.10
InfluxDB shell version: 1.8.10

> CREATE DATABASE sandbox

> SHOW MEASUREMENTS on sandbox
name: measurements
name
----
weather

> use sandbox
Using database sandbox

> SELECT * FROM weather
name: weather
time          humidity wind_direction
----          -------- --------------
3600000000000 30       north

```

### InfluxQL

```sql
create database sandbox
use sandbox

insert sample,type=1 value=10 1663556334
show measurements
show retension policies
select * from sample
```


### Flux言語

InfluxDB 1.8 ではデフォルトで無効化されているので、 conf ファイルで flux を有効にしてある。 参考: [Enable Flux](https://docs.influxdata.com/influxdb/v1.8/flux/installation/)

Fluxのドキュメント: [Get started with Flux | InfluxDB OSS 1.8 Documentation](https://docs.influxdata.com/influxdb/v1.8/flux/get-started/)

```shell
# サーバに接続
$ docker-compose exec influxdb-v1 bash

# `-type=flux` を指定してCLIクライントを起動する
$ influx -type=flux -path-prefix=/api/v2/query
```

## 公式sandbox

* https://github.com/influxdata/sandbox
* https://github.com/influxdata/sandbox/blob/master/documentation/static/tutorials/flux-getting-started.md

```shell
./sandbox up
```

`Explore` で トグルを `Flux` に切り替え、`SCRIPT` ペインでクエリを実行する。

```iflux
from(bucket: "telegraf/autogen")
  |> range(start: v.timeRangeStart, stop: v.timeRangeStop)
  |> filter(fn: (r) =>
    r._measurement == "cpu" and
    r._field == "usage_system" and
    r.cpu == "cpu-total"
  )
  |> yield()
```

