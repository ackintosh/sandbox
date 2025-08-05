* [postgres - Docker Hub](https://hub.docker.com/_/postgres)
* [日本PostgreSQLユーザ会: PostgreSQL 付属ドキュメント](https://www.postgresql.jp/document/current/index.html)


```bash
# adminer
open 'http://localhost:8080/?pgsql=postgres&username=sandbox_user&db=sandbox_db&ns=sandbox_schema'

# psql
psql -h localhost sandbox_db -U sandbox_user

# DBを削除する
docker compose down
docker volume rm postgresql_postgresql-data
```

- [トランザクション分離レベル](./isolation_levels.md)
- [インデックス作成](./create_index.md)
- [TRUCATE TABLE](./truncate_table.md)
- [DELETE](./delete.md)

## データ投入

```sql
# itemテーブルに1,000万件投入する
INSERT INTO sandbox_schema.item (category_id, name, description, created_at)
SELECT
    (random() * 1000)::int,
    md5(random()::text),
    md5(random()::text) || md5(random()::text),
    now() - (random() * interval '365 days')
FROM generate_series(1, 10000000);
```


