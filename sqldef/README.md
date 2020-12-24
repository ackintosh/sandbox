[k0kubun/sqldef: Idempotent MySQL/PostgreSQL schema management by SQL](https://github.com/k0kubun/sqldef)

```shell
# * `postgresql`ディレクトリで `docker-compose up` しておく
#   * そこで作られるネットワーク(postgresql_default)に接続している
# * テスト用に PGSSLMODE=disable を指定

$ docker run \
  --rm \
  --network postgresql_default \
  --env=PGSSLMODE=disable \
  -v (PWD):/tmp/sqldef \
  psqldef sandbox_db -U sandbox_user -W sandbox_pw -f /tmp/sqldef/sandbox_schema.sql -h postgres
```
