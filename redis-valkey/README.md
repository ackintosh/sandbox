

Redis と Valkey でパケット数やサイズに違いがあるか確認。

```bash
# Redis
docker run --rm -p 6379:6379 redis:6.2
# Valkey
docker run --rm -p 6379:6379 valkey/valkey:8.0
```


```bash
# SET 3Bytes
# wireshark_redis_set.csv
# wireshark_valkey_set.csv
redis-cli set test-1 aaa

# GET 3Bytes
# wireshark_redis_get.csv
# wireshark_valkey_get.csv
redis-cli get test-1

# SET 5KB
# wireshark_redis_bench.csv
# wireshark_valkey_bench.csv
redis-benchmark -t set -c 1 -n 1 -d 5000

# GET 5KB
# wireshark_redis_get_5kb.csv
# wireshark_valkey_get_5kb.csv
redis-cli get "key:__rand_int__"


# SET 20KB
# wireshark_redis_bench_20kb.csv
# wireshark_valkey_bench_20kb.csv
redis-benchmark -t set -c 1 -n 1 -d 20000

# GET 20KB
# wireshark_redis_get_20kb.csv
# wireshark_valkey_get_20kb.csv
redis-cli get "key:__rand_int__"

```

