from elasticsearch import Elasticsearch

keywords = ["hardware", "forecast", "architecture"]

es = Elasticsearch("http://localhost:9200/")

features = []
group = []

for k in keywords:
    request = {
            "query": {
                "match": {
                    "title": k
                    }
                },
            "rescore": {
                "query": {
                    "rescore_query": {
                        "sltr": {
                            "params": {
                                "keyword": k
                                },
                            "featureset": "my_featureset"
                            }
                        },
                    "rescore_query_weight": 0.0
                    },
                "window_size": 100
                },
            "ext": {
                "ltr_log": {
                    "log_specs": {
                        "name": "log_entry0",
                        "rescore_index": 0
                        }
                    }
                }
            }
    response = es.search(index="my_index", body=request)
    #print(response)

    group.append(str(len(response["hits"]["hits"])))

    for doc in response["hits"]["hits"]:
        entry = doc["fields"]["_ltrlog"][0]['log_entry0']
        features.append(f"{entry[0]['value']},{entry[1]['value']},{entry[2]['value']}")

print("* feature")
print("\n".join(features))
print("* group")
print("\n".join(group))

