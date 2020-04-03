# Amplify

[Quickstart](https://aws-amplify.github.io/docs/cli-toolchain/quickstart?sdk=js)

2020-04-03 *`amplify init`を実行した時点でAWSにリソースを作る動作をするところが、自分の用途に合わなかったので使っていない*  
(AppSyncをローカルでテストする用途だけに使いたかった)

```bash
# グローバルにインストールしないとamplifyコマンドがバグってしまう
# 2020-04-03時点で試した限り、amplify initコマンドの途中で下記のエラーが出てしまう
# Cannot read property 'value' of undefined

# npm i
# ./node_modules/.bin/amplify

npm install -g @aws-amplify/cli
```
