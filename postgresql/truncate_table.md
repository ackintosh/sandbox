## TRUNCATE TABLE

### TRUCATE TABLE中はテーブルロックが発生する

```sql
-- *** セッションA ***
-- トランザクションを開始して TRUNCATE TABLE を実行する
begin;

truncate table sandbox_schema.item;

```

```sql
-- *** セッションB ***
-- SELECTする
select * from sandbox_schema.item limit 1;
-- → セッションA待ちになる
```



