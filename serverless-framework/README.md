```bash
#npm i
#./node_modules/.bin/serverless

$ npm i -g serverless
$ yarn install
$ sls appsync-offline start
```

### バージョンの組み合わせでエラー?

├─┬ serverless-appsync-offline@1.4.0
└─┬ serverless-appsync-plugin@1.2.0


```bash
$ curl -X POST \
  http://localhost:62222/graphql \
  -H 'Content-Type: application/json' \
  -H 'x-api-key: APIKEY' \
  -d '{
  "query": "{ user(id: 1) { user { id } } }"
}'

{"errorMessage":"Cannot use GraphQLSchema \"[object GraphQLSchema]\" from another module or realm.\n\nEnsure that there is only one instance of \"graphql\" in the node_modules\ndirectory. If different versions of \"graphql\" are the dependencies of other\nrelied on modules, use \"resolutions\" to ensure only one version is installed.\n\nhttps://yarnpkg.com/en/docs/selective-version-resolutions\n\nDuplicate \"graphql\" modules cannot be used at the same time since different\nversions may have different capabilities and behavior. The data from one\nversion used in the function from another could produce confusing and\nspurious results."}⏎ 


$ npm ls graphql

serverless-framework@1.0.0 /Users/***
├─┬ serverless-appsync-offline@1.4.0
│ └─┬ @conduitvc/appsync-emulator-serverless@0.14.5
│   └── UNMET PEER DEPENDENCY graphql@0.13.2
└─┬ serverless-appsync-plugin@1.2.0
  └── graphql@14.6.0

npm ERR! peer dep missing: graphql@^0.10.5 || ^0.11.3 || ^0.12.0 || ^0.13.0, required by graphql-subscriptions@0.5.8
npm ERR! peer dep missing: graphql@^0.13.0, required by graphql-tools@3.1.1
```


##### 参考URL
* [Serverless AppSync Plugin: Top 10 New Features - HackerNoon.com - Medium](https://medium.com/hackernoon/serverless-appsync-plugin-top-10-new-features-3faaf6789480)
* [AppSync + Serverless Frameworkによるソースコードの構成管理 | Takumon Blog](https://takumon.com/aws-appsync-and-serverless-framework)
* serverless.ymlのサンプル(DynamoDB, Serverless FrameworkのOffline supportを使用)
  * https://github.com/serverless/serverless-graphql/tree/master/app-backend/appsync/dynamo
  * https://github.com/serverless/serverless-graphql/blob/master/app-backend/appsync/dynamo/serverless.yml