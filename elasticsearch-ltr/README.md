https://techblog.zozo.com/entry/elasticsearch-learning-to-rank-plugin

https://github.com/ackintosh/elasticsearch-ltr-demo

```
docker compose elasticsearch
```

### feature storeを有効化する

```bash
curl -X PUT http://localhost:9200/_ltr | jq
{
  "acknowledged": true,
  "shards_acknowledged": true,
  "index": ".ltrstore"
}
```

### インデックスのマッピングを登録する

```bash

curl --silent -X PUT -H 'Content-Type: application/json' -d @mapping.json http://localhost:9200/my_index | jq
{
  "acknowledged": true,
  "shards_acknowledged": true,
  "index": "my_index"
}
```

### 特徴量セットを定義する

```bash
curl --silent -X POST  -H 'Content-Type: application/json' -d @featureset.json http://localhost:9200/_ltr/_featureset/my_featureset | jq
{
  "_index": ".ltrstore",
  "_id": "featureset-my_featureset",
  "_version": 1,
  "result": "created",
  "forced_refresh": true,
  "_shards": {
    "total": 1,
    "successful": 1,
    "failed": 0
  },
  "_seq_no": 0,
  "_primary_term": 1
}
```

### ドキュメントを登録する

```bash
curl --silent -X POST 'http://localhost:9200/my_index/_bulk?pretty' -H 'Content-Type: application/json' --data-binary @docs.json
```

```bash
curl --silent -H 'Content-Type: application/json' http://localhost:9200/my_index/_search -d @query_feature.json | jq
```

### 特徴量データを作成

```bash
uv run generate_dataset.py
```

### モデルを作成する

```bash
uv run generate_model.py
```

### モデルをElasticsearchにアップロードする

```bash
curl --silent -X POST -H 'Content-Type: application/json' -d @model.json 'http://localhost:9200/_ltr/_featureset/my_featureset/_createmodel' |jq
```

### リランキング

```bash
curl --silent -H 'Content-Type: application/json' http://localhost:9200/my_index/_search -d @query_rescore.json | jq
```

