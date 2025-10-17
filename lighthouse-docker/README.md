Lighthouse book  
https://lighthouse-book.sigmaprime.io/installation_docker.html

```bash
docker run sigp/lighthouse lighthouse --version

# hoodi
docker run --rm \
  -p 9000:9000/tcp \
  -p 9000:9000/udp \
  -p 9001:9001/udp \
  -p 127.0.0.1:5052:5052 \
  -v $HOME/.lighthouse:/root/.lighthouse \
  sigp/lighthouse lighthouse \
  --network holesky \
  beacon \
  --http \
  --http-address 0.0.0.0 \
  --execution-endpoint http://192.168.11.5:8551

```

