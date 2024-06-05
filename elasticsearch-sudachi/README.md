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

