#!/usr/bin/env bash

# ##################################################
# mv でファイルを上書きする場合、
# * ディレクトリエントリを書き換えるだけで、上書き先のファイルは何も変更しない
# * なので inode 番号を調べると、もとの inode 番号のままであることが確認できる
# ##################################################

echo a > mvtest1
echo b > mvtest2

# inode番号を確認
ls -i mvtest1
ls -i mvtest2

# mv コマンドで, mvtest2 で mvtest1 を上書き
mv mvtest2 mvtest1
# inode番号を確認すると mvtest2 の番号になっている
ls -i mvtest1

# 後片付け
rm mvtest1

