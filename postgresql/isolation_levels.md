# トランザクション分離レベル

## 分離レベル 確認

```sql
sandbox_db=# SHOW TRANSACTION ISOLATION LEVEL;
 transaction_isolation
-----------------------
 read committed
(1 row)
```

## Read uncommitted

- PostgreSQLではこのレベルを指定しても、`Read committed` として扱う

## Read committed (デフォルト)

## Repeatable read

※PostgreSQLの場合は、ファントムリードが発生しない。

#### ファントムリードが発生しない (※PostgreSQLの場合)

SQL標準では、Repeatable readではファントムリードが「発生する」。PostgreSQLが特殊。

```sql
# 分離レベルを REPEATABLE READ に変更
BEGIN TRANSACTION ISOLATION LEVEL REPEATABLE READ;

# weatherテーブルにはレコード無し
select * from sandbox_schema.weather;
 city | temp_lo | temp_hi | prcp | date
------+---------+---------+------+------
(0 rows)

# 別のターミナルで新規レコードを挿入する
begin;
insert into sandbox_schema.weather values ('c', 99, 999, 999, '2025-05-06');
commit;

# 元のターミナルで再度selectしてもレコードは無し
select * from sandbox_schema.weather;
 city | temp_lo | temp_hi | prcp | date
------+---------+---------+------+------
(0 rows)

# トランザクションをロールバックしてから再度selectすると、
# 別ターミナルで挿入したレコードが見れるようになる。
#  → ファントムリードが発生していない
rollback;
select * from sandbox_schema.weather;
 city | temp_lo | temp_hi | prcp |    date
------+---------+---------+------+------------
 c    |      99 |     999 |  999 | 2025-05-06
(1 row)
```

## Serializable


