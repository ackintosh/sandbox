## DELETE

### テーブルの全件削除中でもテーブルロックは発生しない

※ [TRUNCATE TABLEはテーブルロックが発生する](https://github.com/ackintosh/sandbox/blob/master/postgresql/truncate_table.md)

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

