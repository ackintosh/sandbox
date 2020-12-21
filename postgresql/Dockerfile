FROM postgres:13-alpine
ENV LANG ja_JP.utf8

# https://hub.docker.com/_/postgres
# > Initialization scripts
COPY ./initdb/* /docker-entrypoint-initdb.d/
