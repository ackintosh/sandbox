## TRUNCATE TABLE

### TRUCATE TABLE中はテーブルロックが発生する

※ [DELETEの場合はテーブルロックが発生しない](https://github.com/ackintosh/sandbox/blob/master/postgresql/delete.md)

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



