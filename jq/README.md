
[jqを使って少し複雑な条件式でフィルタリングする方法をまとめてみた #Bash - Qiita](https://qiita.com/ttiger55/items/150e9a18313a55841a32)

## select

```bash
cat lighthouse_api_peers.json | jq '.[] | select(.peer_id == "16Uiu2HAmHxqHfsuMuG8PJq82TFVpGFCcu4ZyvSGcvRPKiQWkUzBe")'
```

