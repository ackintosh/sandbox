## ALTER TABLE ... RENAME`

### ALTER TABLE ... RENAME中はテーブルロックが発生する

```sql
-- itemテーブルのコピーを作成. LIKEでインデックスなどの構造もコピーする
CREATE TABLE sandbox_schema.item_copy (LIKE sandbox_schema.item INCLUDING ALL);

-- itemテーブルのレコードをコピー
INSERT INTO sandbox_schema.item_copy SELECT * FROM sandbox_schema.item;

-- リネーム後の動作確認のために item_copy のレコードを更新しておく
UPDATE sandbox_schema.item_copy SET name = 'updated_name' WHERE id = 10;

-- セッションAでトランザクション中に ALTER TABLE ... RENAME を実行する
BEGIN;

ALTER TABLE sandbox_schema.item RENAME TO sandbox_schema.item_old;
ALTER TABLE sandbox_schema.item_copy RENAME TO sandbox_schema.item;

```

```sql
-- セッションBでSELECTする
select * from sandbox_schema.item limit 1;
-- → セッションA待ちになる
```





