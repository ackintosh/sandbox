- [Elasticsearchのための新しい形態素解析器 「Sudachi」 #自然言語処理 - Qiita](https://qiita.com/sorami/items/99604ef105f13d2d472b)

```bash
# sudachiプラグインがインストールされていることを確認
curl -X GET 'http://localhost:9200/_nodes/plugins?pretty' | jq '.nodes[] | .plugins'

# インデックス sudachi_test を作成
curl -X PUT -H "Content-Type: application/json" 'http://localhost:9200/sudachi_test/' -d @analysis_sudachi_settings.json

# 作成したインデックスを確認
curl -X GET 'http://localhost:9200/sudachi_test/?pretty'

# Sudachiプラグインを使った解析
curl -X POST -H "Content-Type: application/json" 'http://localhost:9200/sudachi_test/_analyze?pretty' -d @analyze.json

# インデックス削除
curl -X DELETE 'http://localhost:9200/sudachi_test?pretty=true'
```

## sudachi_c2a

```bash
# インデックス  を作成
curl -X PUT -H "Content-Type: application/json" 'http://localhost:9200/sudachi_c2a/' -d @c2a/create_index.json

# 作成したインデックスを確認
curl -X GET 'http://localhost:9200/sudachi_c2a/?pretty'

# ドキュメントを追加
curl -X POST -H "Content-Type: application/json" 'http://localhost:9200/sudachi_c2a/_bulk?refresh' -d '
{"index":{"_id":"1","_index":"sudachi_c2a"}}
{"sentence": "関西国際空港"}
'

# 検索
curl -X GET -H "Content-Type: application/json" "http://localhost:9200/sudachi_c2a/_search?pretty" \
 -d '
{
    "query": {
        "dis_max": { "queries": [
            { "match": {
                "sentence": {
                    "query": "関西国際空港",
                    "analyzer": "sudachi_a"
                }
            }},
            { "match": {
                "sentence": {
                    "query": "関西国際空港",
                    "analyzer": "sudachi_c"
                }
            }}
        ]}
    },
    "explain": true
}
'

# インデックス削除
curl -X DELETE 'http://localhost:9200/sudachi_c2a?pretty=true'

```
