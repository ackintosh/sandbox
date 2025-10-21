## OpenSearch

https://hub.docker.com/r/opensearchproject/opensearch

## プラグインの確認

Bundled plugins: https://docs.opensearch.org/latest/install-and-configure/plugins/#bundled-plugins

_cat/plugins

```bash
$ curl --silent -X GET "http://localhost:9200/_cat/plugins?v" -ku admin:Super-secret1

name         component                            version
8a379a97a4c4 opensearch-alerting                  2.19.3.0
8a379a97a4c4 opensearch-anomaly-detection         2.19.3.0
8a379a97a4c4 opensearch-asynchronous-search       2.19.3.0
8a379a97a4c4 opensearch-cross-cluster-replication 2.19.3.0
8a379a97a4c4 opensearch-custom-codecs             2.19.3.0
8a379a97a4c4 opensearch-flow-framework            2.19.3.0
8a379a97a4c4 opensearch-geospatial                2.19.3.0
8a379a97a4c4 opensearch-index-management          2.19.3.0
8a379a97a4c4 opensearch-job-scheduler             2.19.3.0
8a379a97a4c4 opensearch-knn                       2.19.3.0
8a379a97a4c4 opensearch-ltr                       2.19.3.0
8a379a97a4c4 opensearch-ml                        2.19.3.0
8a379a97a4c4 opensearch-neural-search             2.19.3.0
8a379a97a4c4 opensearch-notifications             2.19.3.0
8a379a97a4c4 opensearch-notifications-core        2.19.3.0
8a379a97a4c4 opensearch-observability             2.19.3.0
8a379a97a4c4 opensearch-performance-analyzer      2.19.3.0
8a379a97a4c4 opensearch-reports-scheduler         2.19.3.0
8a379a97a4c4 opensearch-security                  2.19.3.0
8a379a97a4c4 opensearch-security-analytics        2.19.3.0
8a379a97a4c4 opensearch-skills                    2.19.3.0
8a379a97a4c4 opensearch-sql                       2.19.3.0
8a379a97a4c4 opensearch-system-templates          2.19.3.0
8a379a97a4c4 query-insights                       2.19.3.0
```

opensearch-plugin list

```bash
$ docker compose exec opensearch bash

[opensearch@8a379a97a4c4 ~]$ ./bin/opensearch-plugin list
opensearch-alerting
opensearch-anomaly-detection
opensearch-asynchronous-search
opensearch-cross-cluster-replication
opensearch-custom-codecs
opensearch-flow-framework
opensearch-geospatial
opensearch-index-management
opensearch-job-scheduler
opensearch-knn
opensearch-ltr
opensearch-ml
opensearch-neural-search
opensearch-notifications
opensearch-notifications-core
opensearch-observability
opensearch-performance-analyzer
opensearch-reports-scheduler
opensearch-security
opensearch-security-analytics
opensearch-skills
opensearch-sql
opensearch-system-templates
query-insights
```

## LTR

https://docs.opensearch.org/latest/search-plugins/ltr/index/


```bash
# https://docs.opensearch.org/latest/search-plugins/ltr/working-with-features/#initializing-the-default-feature-store
$ curl -XPUT "https://localhost:9200/_ltr" -ku admin:Super-secret1
{
  "acknowledged": true,
  "shards_acknowledged": true,
  "index": ".ltrstore"
}

```

## icu_normalizer (token filter)

※要インストール (Dockerfileを参照)

```bash
curl --silent -H "Content-Type: application/json" -X POST 'http://localhost:9200/_analyze' -d '

{
  "tokenizer": "standard",
  "filter": [
    {
      "type": "icu_normalizer",
      "name": "nfkc_cf"
    }
  ],
  "text": "ＡＢＣ①ｶﾀｶﾅé・㍉Ⅲ㎏"
}' | jq

{
  "tokens": [
    {
      "token": "abc",
      "start_offset": 0,
      "end_offset": 3,
      "type": "<ALPHANUM>",
      "position": 0
    },
    {
      "token": "カタカナ",
      "start_offset": 4,
      "end_offset": 8,
      "type": "<KATAKANA>",
      "position": 1
    },
    {
      "token": "é",
      "start_offset": 8,
      "end_offset": 9,
      "type": "<ALPHANUM>",
      "position": 2
    },
    {
      "token": "ミリ",
      "start_offset": 10,
      "end_offset": 11,
      "type": "<KATAKANA>",
      "position": 3
    },
    {
      "token": "iii",
      "start_offset": 11,
      "end_offset": 12,
      "type": "<ALPHANUM>",
      "position": 4
    }
  ]
}
```


