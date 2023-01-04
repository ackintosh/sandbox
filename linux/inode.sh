#!/usr/bin/env bash

echo > inodetest.txt

# inode番号を確認する
ls -i inodetest.txt


# 後片付け
rm inodetest.txt

