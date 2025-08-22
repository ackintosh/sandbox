# Grafana + Tempo

```bash
 RUST_MIN_STACK=4194304 lighthouse bn \
  --execution-endpoint http://127.0.0.1:8551 \
  --execution-jwt /tmp/mock-el-jwt.secret \
  --checkpoint-sync-url https://checkpoint-sync.holesky.ethpandaops.io/ \
  --disable-deposit-contract-sync --metrics --network holesky --telemetry-collector-url http://localhost:4317

 RUST_MIN_STACK=4194304 lighthouse bn \
  --execution-endpoint http://127.0.0.1:8551 \
  --execution-jwt /tmp/mock-el-jwt.secret \
  --checkpoint-sync-url https://checkpoint-sync.holesky.ethpandaops.io/ \
  --disable-deposit-contract-sync --metrics --network holesky --telemetry-collector-url http://localhost:4318/v1/traces
```

```bash
# Open Grafana
open http://localhost:3000
# admin / admin
```

Conections -> Add data source -> Tempo  
URL: http://tempo:3200

