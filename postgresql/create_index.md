# インデックス作成

```sql
# インデックス作成中のロック状態を確認する
SELECT
  a.pid,
  a.query,
  a.state,
  l.locktype,
  l.mode,
  l.granted,
  c.relname AS relation
FROM
  pg_locks l
JOIN
  pg_stat_activity a ON l.pid = a.pid
LEFT JOIN
  pg_class c ON l.relation = c.oid
WHERE
  c.relname like '%item';

# インデックス確認
\d sandbox_schema.item

# 削除
DROP INDEX sandbox_schema.idx_item_category_id;

```

## CREATE INDEX

```sql
CREATE INDEX idx_item_category_id ON sandbox_schema.item(category_id);
  -> Time: 2179.909 ms (00:02.180)

# CREATE INDEX 実行中のロック状態
 pid |                                 query                                  | state  | locktype |   mode    | granted | relation
-----+------------------------------------------------------------------------+--------+----------+-----------+---------+----------
  93 | CREATE INDEX idx_item_category_id ON sandbox_schema.item(category_id); | active | relation | ShareLock | t       | item
 116 | CREATE INDEX idx_item_category_id ON sandbox_schema.item(category_id); | active | relation | ShareLock | t       | item
(2 rows)

ShareLockなので：

- SELECTは可能 `select * from sandbox_schema.item where id = 1;`
- UPDATEはブロックされる `update sandbox_schema.item set name = 'test item' where id = 1;`

```

## CREATE INDEX CONCURRENTLY

```sql
\timing
CREATE INDEX CONCURRENTLY idx_item_category_id ON sandbox_schema.item(category_id);
  -> Time: 3655.294 ms (00:03.655)

# CREATE INDEX CONCURRENTLY 実行中のロック状態
 pid |                                        query                                        | state  | locktype |           mode           | granted | relation
-----+-------------------------------------------------------------------------------------+--------+----------+--------------------------+---------+----------
  93 | CREATE INDEX CONCURRENTLY idx_item_category_id ON sandbox_schema.item(category_id); | active | relation | ShareUpdateExclusiveLock | t       | item
 154 | CREATE INDEX CONCURRENTLY idx_item_category_id ON sandbox_schema.item(category_id); | active | relation | ShareUpdateExclusiveLock | t       | item
(2 rows)

ShareUpdateExclusiveLockなので：

- SELECT可能 `select * from sandbox_schema.item where id = 1;`
- UPDATEも可能 `update sandbox_schema.item set name = 'test item' where id = 1;`
```

