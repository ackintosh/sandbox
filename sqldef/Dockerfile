# https://hub.docker.com/r/amothic/mysqldef/dockerfile
FROM ubuntu:21.04 as builder

ENV VERSION 0.8.7

RUN set -ex \
    && apt-get update \
    && apt-get install -y curl \
    && curl -fSL https://github.com/k0kubun/sqldef/releases/download/v$VERSION/psqldef_linux_amd64.tar.gz -o psqldef.tar.gz \
    && tar -zxf psqldef.tar.gz

# alpineだと(おそらく共有ライブラリが無い理由で) 実行時に no such file or directory のエラーになってしまうので
# ubuntuにしている
FROM ubuntu:21.04
COPY --from=builder /psqldef /usr/local/bin/psqldef
ENTRYPOINT ["psqldef"]
