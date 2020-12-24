[k0kubun/sqldef: Idempotent MySQL/PostgreSQL schema management by SQL](https://github.com/k0kubun/sqldef)

#### docker build (alpine)

```shell
$ docker build -t psqldef:0.8.6-alpine -f Dockerfile.alpine . 
```

#### push the image to GitHub Container Registry

https://docs.github.com/ja/free-pro-team@latest/packages/guides/pushing-and-pulling-docker-images

```shell
$ docker tag {IMAGE ID} ghcr.io/ackintosh/psqldef:0.8.6-alpine
$ docker push ghcr.io/ackintosh/psqldef:0.8.6-alpine
```

#### run psqldef

```shell
# * `postgresql`$B%G%#%l%/%H%j$G(B `docker-compose up` $B$7$F$*$/(B
#   * $B$=$3$G:n$i$l$k%M%C%H%o!<%/(B(postgresql_default)$B$K@\B3$7$F$$$k(B
# * $B%F%9%HMQ$K(B PGSSLMODE=disable $B$r;XDj(B

$ docker run \
  --rm \
  --network postgresql_default \
  --env=PGSSLMODE=disable \
  -v (PWD):/tmp/sqldef \
  psqldef sandbox_db -U sandbox_user -W sandbox_pw -f /tmp/sqldef/sandbox_schema.sql -h postgres
```
