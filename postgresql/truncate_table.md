## TRUNCATE TABLE

### TRUCATE TABLE中はテーブルロックが発生する

```sql
-- セッションAでトランザクション中に TRUNCATE TABLE を実行する
begin;

truncate table sandbox_schema.item;

```

```sql
-- セッションBでSELECTする
select * from sandbox_schema.item limit 1;
-- → セッションA待ちになる
```



