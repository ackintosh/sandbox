## DELETE


```sql
-- *** セッションA ***
-- トランザクションを開始して DELETE でテーブルのレコード全体を削除する
begin;
delete from sandbox_schema.item;

```

```sql
-- *** セッションB ***
-- SELECTする
select * from sandbox_schema.item limit 1;
-- → 1行取得できる（セッションAにブロックされない）
```

