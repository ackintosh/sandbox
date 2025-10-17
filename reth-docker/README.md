
https://reth.rs/installation/docker/

```bash

docker run --rm ghcr.io/paradigmxyz/reth --version

docker run --rm \
    -v rethdata:/root/.local/share/reth/mainnet \
    -p 9001:9001 \
    -p 30303:30303 \
    -p 30303:30303/udp \
    --name reth \
    ghcr.io/paradigmxyz/reth \
    node \
    --metrics 0.0.0.0:9001

# RUST_LOG_STYLE=never でログの色付けを無効化
docker run --rm \
    -v rethdata:/root/.local/share/reth/mainnet \
    -p 9001:9001 \
    -p 30303:30303 \
    -p 30303:30303/udp \
    -e RUST_LOG_STYLE=never \
    --name reth \
    ghcr.io/paradigmxyz/reth \
    node \
    --metrics 0.0.0.0:9001

```

