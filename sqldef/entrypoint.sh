#!/bin/sh

set -euo pipefail

# sqldefはデフォルトでDDLを反映しますが、
# このスクリプトではデフォルトをdry-runにしていて、DDLを反映するには --no-dry-run を指定するようにしています。
# 理由は、下記の使い方をしたかったからです。
# 1. `docker-compose up` で起動時に dry-run の結果をコンソールに出力する
# 2. DDLを反映したい場合は、--no-dry-run を明示的に指定してsqldefコンテナを実行する
DRY_RUN='--dry-run'

if [ $# -eq 1 ] && [ $1 == '--no-dry-run' ]; then
  DRY_RUN=''
fi

HOST="${PGHOST:-postgres-local}"

# NOTE: 現状ローカルでしか使っていないのでユーザ名などは直書きしています

for DB in $(echo $POSTGRES_MULTIPLE_DATABASES | tr ',' ' '); do
  echo -e "\033[0;32m------------------------------\033[0m"
  echo -e "\033[0;32mRunning sqldef for $DB \033[0m"
  echo -e "\033[0;32m------------------------------\033[0m"

  cat sqldef/*.sql | psqldef \
    $DB \
    -U sandbox_user \
    -W sandbox_passwrod \
    -h $HOST \
    --skip-drop \
    $DRY_RUN
done

