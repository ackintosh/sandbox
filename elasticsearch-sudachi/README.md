## 公式ドキュメント

- [Analyze API | Elasticsearch Guide [8.15] | Elastic](https://www.elastic.co/guide/en/elasticsearch/reference/current/indices-analyze.html)
- [Term vectors API | Elasticsearch Guide [8.15] | Elastic](https://www.elastic.co/guide/en/elasticsearch/reference/current/docs-termvectors.html)

## インデクス作成 & 削除

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

## sudachi_split

https://github.com/WorksApplications/elasticsearch-sudachi?tab=readme-ov-file#sudachi_split

CモードとAモード併用できるToken Filter。

#### 参考：CモードとAモードの解析結果

```bash
# Cモード
$ echo 関西国際空港 | java -jar sudachi-0.7.3.jar -m C
関西国際空港    名詞,固有名詞,一般,*,*,*        関西国際空港
EOS

# Aモード
$ echo 関西国際空港 | java -jar sudachi-0.7.3.jar -m A
関西    名詞,固有名詞,地名,一般,*,*     関西
国際    名詞,普通名詞,一般,*,*,*        国際
空港    名詞,普通名詞,一般,*,*,*        空港
EOS
```

#### sudachi_splitを使ってインデックスを作成する

```bash
# インデックスを作成
curl -X PUT -H "Content-Type: application/json" 'http://localhost:9200/sudachi_split/' -d @sudachi_split/create_index.json

# ドキュメントを追加
curl -X POST -H "Content-Type: application/json" 'http://localhost:9200/sudachi_split/_bulk?refresh' -d '
{"index":{"_id":"1","_index":"sudachi_split"}}
{"sentence": "関西国際空港"}
{"index":{"_id":"2","_index":"sudachi_split"}}
{"sentence": "成田国際空港"}
' | jq

# Analyze APIを使って `sudachi_split` analyzerの動作確認
#   -> C単位とA単位 両方のトークンが出力される
curl -X GET "localhost:9200/sudachi_split/_analyze?pretty" -H 'Content-Type: application/json' -d'{"analyzer":"sudachi_split", "text" : "関西国際空港"}'
{
  "tokens" : [
    {
      "token" : "関西国際空港",
      "start_offset" : 0,
      "end_offset" : 6,
      "type" : "word",
      "position" : 0,
      "positionLength" : 3
    },
    {
      "token" : "関西",
      "start_offset" : 0,
      "end_offset" : 2,
      "type" : "word",
      "position" : 0
    },
    {
      "token" : "国際",
      "start_offset" : 2,
      "end_offset" : 4,
      "type" : "word",
      "position" : 1
    },
    {
      "token" : "空港",
      "start_offset" : 4,
      "end_offset" : 6,
      "type" : "word",
      "position" : 2
    }
  ]
}

# Term vectors APIでインデックスされている単語を確認する
#  -> ドキュメントID:1
#  -> C単位とA単位 両方でインデックスされている
curl -H 'Content-Type: application/json' -XGET "localhost:9200/sudachi_split/_termvectors/1" | jq
{
  "_index": "sudachi_split",
  "_id": "1",
  "_version": 1,
  "found": true,
  "took": 0,
  "term_vectors": {
    "sentence": {
      "field_statistics": {
        "sum_doc_freq": 8,
        "doc_count": 2,
        "sum_ttf": 8
      },
      "terms": {
        "国際": {
          "term_freq": 1,
          "tokens": [
            {
              "position": 1,
              "start_offset": 2,
              "end_offset": 4
            }
          ]
        },
        "空港": {
          "term_freq": 1,
          "tokens": [
            {
              "position": 2,
              "start_offset": 4,
              "end_offset": 6
            }
          ]
        },
        "関西": {
          "term_freq": 1,
          "tokens": [
            {
              "position": 0,
              "start_offset": 0,
              "end_offset": 2
            }
          ]
        },
        "関西国際空港": {
          "term_freq": 1,
          "tokens": [
            {
              "position": 0,
              "start_offset": 0,
              "end_offset": 6
            }
          ]
        }
      }
    }
  }
}

```


## sudachi_c2a

CモードとAモードを併用する。

参考：https://github.com/WorksApplications/elasticsearch-sudachi/issues/75#issuecomment-2134190251

```bash
# インデックス sudachi_c2a を作成
<C & Aモード>
curl -X PUT -H "Content-Type: application/json" 'http://localhost:9200/sudachi_c2a/' -d @c2a/create_index.json
<Aモード>
curl -X PUT -H "Content-Type: application/json" 'http://localhost:9200/sudachi_a/' -d @c2a/create_index_a.json

# 作成したインデックスを確認
curl -X GET 'http://localhost:9200/sudachi_c2a/?pretty'
curl -X GET 'http://localhost:9200/sudachi_a/?pretty'

# ドキュメントを追加
<C & Aモード>
curl -X POST -H "Content-Type: application/json" 'http://localhost:9200/sudachi_c2a/_bulk?refresh' -d '
{"index":{"_id":"1","_index":"sudachi_c2a"}}
{"sentence": "関西国際空港"}
{"index":{"_id":"2","_index":"sudachi_c2a"}}
{"sentence": "成田国際空港"}
' | jq

<Aモード>
curl -X POST -H "Content-Type: application/json" 'http://localhost:9200/sudachi_a/_bulk?refresh' -d '
{"index":{"_id":"1","_index":"sudachi_a"}}
{"sentence": "関西国際空港"}
'

# 検索
<C & Aモード>
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
' | jq

<Aモード>
curl -X GET -H "Content-Type: application/json" "http://localhost:9200/sudachi_a/_search?pretty" \
 -d '
{
    "query": {
        "dis_max": { "queries": [
            { "match": {
                "sentence": {
                    "query": "関西国際空港",
                    "analyzer": "sudachi_a"
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

## 実験：CモードでインデックスしてAモードで検索

```bash
# インデックスを作成
curl -X PUT -H "Content-Type: application/json" 'http://localhost:9200/c_index_a_search/' -d @c_index_a_search/create_index.json

# ドキュメントを追加
curl -X POST -H "Content-Type: application/json" 'http://localhost:9200/c_index_a_search/_bulk?refresh' -d '
{"index":{"_id":"1","_index":"c_index_a_search"}}
{"sentence": "関西国際空港"}
{"index":{"_id":"2","_index":"c_index_a_search"}}
{"sentence": "成田国際空港"}
{"index":{"_id":"3","_index":"c_index_a_search"}}
{"sentence": "売店"}
' | jq

# Term vectors APIでインデックスされている単語を確認する
#  -> ドキュメントID:1
#  -> Cモード
curl -H 'Content-Type: application/json' -XGET "localhost:9200/c_index_a_search/_termvectors/1" | jq
{
  "_index": "c_index_a_search",
  "_id": "1",
  "_version": 1,
  "found": true,
  "took": 0,
  "term_vectors": {
    "sentence": {
      "field_statistics": {
        "sum_doc_freq": 2,
        "doc_count": 2,
        "sum_ttf": 2
      },
      "terms": {
        "関西国際空港": {
          "term_freq": 1,
          "tokens": [
            {
              "position": 0,
              "start_offset": 0,
              "end_offset": 6
            }
          ]
        }
      }
    }
  }
}

#  -> ドキュメントID:3
#  -> Cモード
curl -H 'Content-Type: application/json' -XGET "localhost:9200/c_index_a_search/_termvectors/3" | jq
{
  "_index": "c_index_a_search",
  "_id": "3",
  "_version": 2,
  "found": true,
  "took": 1,
  "term_vectors": {
    "sentence": {
      "field_statistics": {
        "sum_doc_freq": 6,
        "doc_count": 6,
        "sum_ttf": 6
      },
      "terms": {
        "売店": {
          "term_freq": 1,
          "tokens": [
            {
              "position": 0,
              "start_offset": 0,
              "end_offset": 2
            }
          ]
        }
      }
    }
  }
}

# 検索（Aモード） クエリ：関西国際空港
curl -X GET -H "Content-Type: application/json" "http://localhost:9200/c_index_a_search/_search?pretty" \
 -d '
{
    "query": {
        "match": {
            "sentence": {
                "query": "関西国際空港",
                "analyzer": "sudachi_a"
            }
        }
    },
    "explain": true
}
'
## -> ノーヒット
##   -> 関西国際空港のA単位は [関西, 国際, 空港] なので、ドキュメント1の 関西国際空港 にマッチしない
{
  "took" : 2,
  "timed_out" : false,
  "_shards" : {
    "total" : 1,
    "successful" : 1,
    "skipped" : 0,
    "failed" : 0
  },
  "hits" : {
    "total" : {
      "value" : 0,
      "relation" : "eq"
    },
    "max_score" : null,
    "hits" : [ ]
  }
}

# 検索（Aモード） クエリ：売店
curl -X GET -H "Content-Type: application/json" "http://localhost:9200/c_index_a_search/_search?pretty" \
 -d '
{
    "query": {
        "match": {
            "sentence": {
                "query": "売店",
                "analyzer": "sudachi_a"
            }
        }
    },
    "explain": true
}
' | jq
## -> ドキュメントID:3がヒット
##  -> クエリ：売店のA単位は「売店」なのでドキュメントID3とマッチする
{
  "took" : 2,
  "timed_out" : false,
  "_shards" : {
    "total" : 1,
    "successful" : 1,
    "skipped" : 0,
    "failed" : 0
  },
  "hits" : {
    "total" : {
      "value" : 1,
      "relation" : "eq"
    },
    "max_score" : 1.540445,
    "hits" : [
      {
        "_shard" : "[c_index_a_search][0]",
        "_node" : "cagRlSDmT9ydtCPn4CkSPQ",
        "_index" : "c_index_a_search",
        "_id" : "3",
        "_score" : 1.540445,
        "_source" : {
          "sentence" : "売店"
        },
        "_explanation" : {
          "value" : 1.540445,
          "description" : "weight(sentence:売店 in 2) [PerFieldSimilarity], result of:",
          "details" : [
            {
              "value" : 1.540445,
              "description" : "score(freq=1.0), computed as boost * idf * tf from:",
              "details" : [
                {
                  "value" : 2.2,
                  "description" : "boost",
                  "details" : [ ]
                },
                {
                  "value" : 1.5404451,
                  "description" : "idf, computed as log(1 + (N - n + 0.5) / (n + 0.5)) from:",
                  "details" : [
                    {
                      "value" : 1,
                      "description" : "n, number of documents containing term",
                      "details" : [ ]
                    },
                    {
                      "value" : 6,
                      "description" : "N, total number of documents with field",
                      "details" : [ ]
                    }
                  ]
                },
                {
                  "value" : 0.45454544,
                  "description" : "tf, computed as freq / (freq + k1 * (1 - b + b * dl / avgdl)) from:",
                  "details" : [
                    {
                      "value" : 1.0,
                      "description" : "freq, occurrences of term within document",
                      "details" : [ ]
                    },
                    {
                      "value" : 1.2,
                      "description" : "k1, term saturation parameter",
                      "details" : [ ]
                    },
                    {
                      "value" : 0.75,
                      "description" : "b, length normalization parameter",
                      "details" : [ ]
                    },
                    {
                      "value" : 1.0,
                      "description" : "dl, length of field",
                      "details" : [ ]
                    },
                    {
                      "value" : 1.0,
                      "description" : "avgdl, average length of field",
                      "details" : [ ]
                    }
                  ]
                }
              ]
            }
          ]
        }
      }
    ]
  }
}

```


