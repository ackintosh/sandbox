[k0kubun/sqldef: Idempotent MySQL/PostgreSQL schema management by SQL](https://github.com/k0kubun/sqldef)

#### docker build

```shell
# alpine
$ docker build -t psqldef:0.8.7-alpine -f Dockerfile.alpine . 
$ docker build -t psqldef:0.8.7-alpine-using-builder -f Dockerfile.alpine-using-builder . 

# ubuntu
$ docker build -t psqldef:0.8.7 . 
```

image size

```shell
psqldef         0.8.7                        2fa00184f195   8 seconds ago   86.7MB
psqldef         0.8.7-alpine                 eece920587b2   5 minutes ago   22MB
psqldef         0.8.7-alpine-using-builder   2611209f48b7   5 minutes ago   22MB
```

#### push the image to GitHub Container Registry

https://docs.github.com/ja/free-pro-team@latest/packages/guides/pushing-and-pulling-docker-images

```shell
$ docker tag {IMAGE ID} ghcr.io/ackintosh/psqldef:0.8.6-alpine
$ docker push ghcr.io/ackintosh/psqldef:0.8.6-alpine
```
#### GitHub Actionsでの実行

- https://github.com/ackintosh/sandbox/blob/master/.github/workflows/phpunit.yaml

#### ローカルでの実行

```shell
# * `postgresql`ディレクトリで `docker-compose up` しておく
#   * そこで作られるネットワーク(postgresql_default)に接続している
# * テスト用に PGSSLMODE=disable を指定

$ docker run \
  --rm \
  --network postgresql_default \
  --env=PGSSLMODE=disable \
  -v (PWD):/tmp/sqldef \
  psqldef sandbox_db -U sandbox_user -W sandbox_pw -f /tmp/sqldef/sandbox_schema.sql -h postgres
```
