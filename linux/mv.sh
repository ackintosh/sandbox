#!/usr/bin/env bash

# ##################################################
# mv でファイルを上書きする場合、
# * ディレクトリエントリを書き換えるだけで、上書き先のファイルは何も変更しない
# * なので inode 番号を調べると、もとの inode 番号のままであることが確認できる
# ##################################################
echo 'テスト1開始'

echo 'ファイルを作成'
echo a > mvtest1
echo -n 'mvtest1: '
cat mvtest1
echo b > mvtest2
echo -n 'mvtest2: '
cat mvtest2

echo 'inode番号を確認'
ls -i mvtest1
ls -i mvtest2

# mv コマンドで, mvtest2 で mvtest1 を上書き
mv mvtest2 mvtest1
echo 'mvコマンドで上書き完了'

echo 'inode番号を再確認'
# inode番号を確認すると mvtest2 の番号になっている
ls -i mvtest1

# 後片付け
rm mvtest1
echo 'テスト1完了'
echo ''


# ##################################################
# ただし、異なるボリューム間でのmvコマンドの場合は、
# cpコマンドと同じ動きになる。
#   → inodeを上書きする
# ##################################################
echo 'テスト2開始'

# 別々のボリュームにファイルを作成する
echo 'ファイルを作成'
echo a > /tmp/mvtest1
echo -n '/tmp/mvtest1: '
cat /tmp/mvtest1
# sudo echo b >> mvtest2 だと、echoにはsudoが効くが、リダイレクトには聞かないのでPermission Deniedになってしまう
# なので、代わりに tee を使っている
echo b | sudo tee /media/akihito/writable/mvtest2 > /dev/null
echo -n '/media/akihito/writable/mvtest2: '
cat /media/akihito/writable/mvtest2


echo 'inode番号を確認'
ls -i /tmp/mvtest1
# 出力例: 17563654 /tmp/mvtest1
ls -i /media/akihito/writable/mvtest2
# 出力例: 12 /media/akihito/writable/mvtest2

# mv コマンドで上書き
sudo mv /media/akihito/writable/mvtest2 /tmp/mvtest1
echo 'mvコマンドで上書き完了'

echo 'inode番号を再確認'
ls -i /tmp/mvtest1
# 出力例: 17563654 /tmp/mvtest1
#  → mvコマンドの前とinode番号が同じ = 同一inodeが上書きされた

# 後片付け
sudo rm /tmp/mvtest1
echo 'テスト2完了'
echo ''

