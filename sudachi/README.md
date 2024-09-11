
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

# 表記正規化(Normalized Form)
# https://github.com/WorksApplications/Sudachi?tab=readme-ov-file#normalized-form
# 例: 打込む → 打ち込む
$ echo 打込む | java -jar sudachi-0.7.3.jar -m C
打込む  動詞,一般,*,*,五段-マ行,終止形-一般     打ち込む
EOS

```

## ユーザー辞書

https://github.com/WorksApplications/Sudachi/blob/develop/docs/user_dict.md#%E3%83%90%E3%82%A4%E3%83%8A%E3%83%AA%E8%BE%9E%E6%9B%B8%E3%81%AE%E4%BD%9C%E6%88%90

```bash
# ユーザー辞書をコンパイル
java -Dfile.encoding=UTF-8 -cp sudachi-0.7.3.jar com.worksap.nlp.sudachi.dictionary.UserDictionaryBuilder -o user.dic -s system_core.dic user.csv

# ユーザー辞書を使用して形態素解析する
## ユーザー辞書なし
### A単位
echo 透明マスク | java -jar sudachi-0.7.3.jar -m A --systemDict system_core.dic
透明    形状詞,一般,*,*,*,*     透明
マスク  名詞,普通名詞,一般,*,*,*        マスク
EOS
### C単位
echo 透明マスク | java -jar sudachi-0.7.3.jar -m C --systemDict system_core.dic
透明    形状詞,一般,*,*,*,*     透明
マスク  名詞,普通名詞,一般,*,*,*        マスク
EOS


## ユーザー辞書あり  -> 固有名詞として分割される
### A単位
echo 透明マスク | java -jar sudachi-0.7.3.jar -m A --systemDict system_core.dic --userDict user.dic
透明マスク      名詞,固有名詞,一般,*,*,*        透明マスク
EOS

### C単位
echo 透明マスク | java -jar sudachi-0.7.3.jar -m C --systemDict system_core.dic --userDict user.dic
透明マスク      名詞,固有名詞,一般,*,*,*        透明マスク
EOS

```

