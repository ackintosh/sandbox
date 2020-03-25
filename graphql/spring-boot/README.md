# GraphQL

1. 起動する
1. GraphiQLでクエリを発行してみる http://localhost:8080/graphiql

#### クエリ(例)
```graphql
{
  # id:1のおすすめを取得する
  recommend(id: 1) {
    name
    items {
      id
      name
    }
  }
  
  # 全てのおすすめを取得する
  recommends {
    id
    name
    items {
      id
      name
    }
  }
}
```

#### 結果(例)

```
{
  "data": {
    "recommend": {
      "name": "テレワークにお役立ちのアイテム集合！",
      "items": [
        {
          "id": "1",
          "name": "トートバッグ"
        },
        {
          "id": "2",
          "name": "クッションケース"
        }
      ]
    },
    "recommends": [
      {
        "id": "1",
        "name": "テレワークにお役立ちのアイテム集合！",
        "items": [
          {
            "id": "1",
            "name": "トートバッグ"
          },
          {
            "id": "2",
            "name": "クッションケース"
          }
        ]
      },
      {
        "id": "2",
        "name": "わけあり商品！",
        "items": [
          {
            "id": "3",
            "name": "折りたたみテーブル"
          },
          {
            "id": "4",
            "name": "ホワイトボード"
          }
        ]
      }
    ]
  }
}
```

#### N+1問題

おすすめに含まれる商品の情報を取得するときにN+1問題が起きてしまうのを防ぐために [Dataloader](https://github.com/graphql-java/java-dataloader) を使用。

* 商品情報を取るためのDataloader ([ItemDataLoader](https://github.com/ackintosh/sandbox/blob/master/graphql/spring-boot/src/main/kotlin/com/github/ackintosh/graphql/dataloader/ItemDataLoader.kt))
* 実装したDataloaderを登録しておく ([CustomGraphQLContextBuilder](https://github.com/ackintosh/sandbox/blob/master/graphql/spring-boot/src/main/kotlin/com/github/ackintosh/graphql/CustomGraphQLContextBuilder.kt))
* ItemDataloaderを通して商品情報を取得する ([ItemResolver](https://github.com/ackintosh/sandbox/blob/master/graphql/spring-boot/src/main/kotlin/com/github/ackintosh/graphql/resolver/ItemResolver.kt))

![image](https://user-images.githubusercontent.com/1885716/77497714-5561af80-6e91-11ea-874b-ed9b82cdedc0.png)

## Schema設計の参考URL

#### GraphQL APIを公開しているサービス
* [APIs-guru/graphql-apis: 📜 A collective list of public GraphQL APIs](https://github.com/APIs-guru/graphql-apis)

#### ベストプラクティス
* [GraphQL Best Practices | GraphQL](https://graphql.org/learn/best-practices/)
* [GraphQL best practices for GraphQL schema design](https://atheros.ai/blog/graphql-best-practices-for-graphql-schema-design)
* [vvakame/graphql-schema-guide: GraphQLスキーマのあれこれをいい感じにする本](https://github.com/vvakame/graphql-schema-guide)
  * `1.3 命名規則について`

## コード生成
* [Kotlin · GraphQL Code Generator](https://graphql-code-generator.com/docs/plugins/kotlin)
* [graphql-code-generatorでフロントエンドとバックエンドで型を共有するのをやってみた](https://medium.com/@omu.omugin/graphql-code-generator%E3%81%A7%E3%83%95%E3%83%AD%E3%83%B3%E3%83%88%E3%82%A8%E3%83%B3%E3%83%89%E3%81%A8%E3%83%90%E3%83%83%E3%82%AF%E3%82%A8%E3%83%B3%E3%83%89%E3%81%A7%E5%9E%8B%E3%82%92%E5%85%B1%E6%9C%89%E3%81%99%E3%82%8B%E3%81%AE%E3%82%92%E3%82%84%E3%81%A3%E3%81%A6%E3%81%BF%E3%81%9F-775e953cc8)

## 参考にしたサンプルコード
* https://github.com/graphql-java-kickstart/graphql-spring-boot/tree/master/example-request-scoped-dataloader
* [marshi/graphql-sample: graphql-spring-bootのサンプルコードです](https://github.com/marshi/graphql-sample)

