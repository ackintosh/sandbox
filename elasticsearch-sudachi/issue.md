https://github.com/WorksApplications/elasticsearch-sudachi/issues/142

```bash
# Analyzerの動作確認
curl -X GET "localhost:9200/_analyze?pretty" -H 'Content-Type: application/json' -d '{"tokenizer":"sudachi_tokenizer", "text" : "関西国際空港", "explain": true}'
```

