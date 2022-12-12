#!/bin/bash
set -euo pipefail

bar=

# "${bar}" (ハイフン無し）の場合、変数が未定義だとエラーになる
while [[ -z "${bar-}" ]]; do
  echo 123
  bar=aaaa
  sleep 1
done 

