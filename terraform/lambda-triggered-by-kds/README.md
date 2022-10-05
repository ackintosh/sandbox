## Kinesis Data Stream のイベントを Lambda 関数で処理する

```shell
# Lambda関数として登録するプログラムをビルドする
make

# AWSリソースを作成する
terraform apply

# イベントレコードを Kinesis Stream に追加する
aws kinesis put-record \
  --stream-name lambda-stream \
  --partition-key 1 \
  --data "Hello, this is a test." \
  --cli-binary-format raw-in-base64-out
# --> CloudWatchログで出力を確認する

# lambda関数を更新する場合
make update-lambda-function
```
