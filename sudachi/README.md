
チュートリアル
https://github.com/WorksApplications/Sudachi/blob/develop/docs/tutorial.md

リリース
https://github.com/WorksApplications/Sudachi/releases

## セットアップ

※ sudachi.jsonをリポジトリに入れているが、デフォルトのまま

```bash
# sudachiをダウンロード
curl --output sudachi-0.7.3-executable.zip -L https://github.com/WorksApplications/Sudachi/releases/download/v0.7.3/sudachi-0.7.3-executable.zip
unzip sudachi-0.7.3-executable.zip

# 辞書をダウンロード
curl --output sudachi-dictionary-latest-core.zip -L http://sudachi.s3-website-ap-northeast-1.amazonaws.com/sudachidict/sudachi-dictionary-latest-core.zip
unzip sudachi-dictionary-latest-core.zip

# ダウンロードした辞書をsudachi実行ファイル(jar)と同一ディレクトリに移動する
#  → ルートディレクトリに jar が展開されているのでひとつ上のディレクトリに移動する
mv sudachi-dictionary-20240409/system_core.dic ./
```

## 実行

```bash
$ echo 医薬品安全管理責任者 | java -jar sudachi-0.7.3.jar
医薬品  名詞,普通名詞,一般,*,*,*        医薬品
安全    名詞,普通名詞,形状詞可能,*,*,*  安全
管理責任者      名詞,普通名詞,一般,*,*,*        管理責任者
EOS

# Aモードで実行
$ echo 医薬品安全管理責任者 | java -jar sudachi-0.7.3.jar -m A
医薬    名詞,普通名詞,一般,*,*,*        医薬
品      接尾辞,名詞的,一般,*,*,*        品
安全    名詞,普通名詞,形状詞可能,*,*,*  安全
管理    名詞,普通名詞,サ変可能,*,*,*    管理
責任    名詞,普通名詞,一般,*,*,*        責任
者      接尾辞,名詞的,一般,*,*,*        者
EOS

# 正規化(Normalized Form)
# https://github.com/WorksApplications/Sudachi?tab=readme-ov-file#normalized-form
# 例: 打込む → 打ち込む
$ echo 打込む | java -jar sudachi-0.7.3.jar -m C
打込む  動詞,一般,*,*,五段-マ行,終止形-一般     打ち込む
EOS

```

