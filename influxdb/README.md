
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


