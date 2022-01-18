#!/usr/bin/env bash

set -Eeuo pipefail

# #################################################
# プロセスが存在すれば kill コマンドで終了させる
# #################################################
PID=48937

# 下記のように $? でステータスコードを確認するのは良くない
# ps -p $PID > /dev/null
# if [ $? -eq 0 ]; then
# 参考:
# https://github.com/koalaman/shellcheck/wiki/SC2181

if ps -p $PID > /dev/null; then
	kill $PID
	echo "killed $PID."
else
	echo "PID $PID is already terminated."
fi

