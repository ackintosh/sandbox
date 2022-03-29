https://github.com/sigp/lighthouse-metrics の設定ファイルに自分用の修正を加えたもの。

Macのローカル（Dockerではなく）で動かすために修正した。


## prometheus

#### インストール

- https://prometheus.io/download/ からダウンロードする

#### 設定ファイルを配置

```bash
$ cd ~/Downloads/prometheus-2.24.1.darwin-amd64
$ ln -s ~/src/github.com/ackintosh/sandbox/lighthouse-metrics/prometheus.yml prometheus.yml
```

#### 起動

```bash
$ cd ~/Downloads/prometheus-2.24.1.darwin-amd64
$ ./prometheus
```

#### 確認

- http://localhost:9090/targets


## grafana

#### 修正点

ダッシュボードのJSONファイルをそのまま使っただけでは、  
`Datasource named ${DS_PROMETHEUS} was not found`  
というエラーがブラウザのコンソールに表示され、画面にグラフが描画されない。

なので https://github.com/grafana/grafana/issues/10786#issuecomment-568788499 を参考にして `templating` の設定を下記にした。

```json
"templating": {
  "list": [
    {
      "hide": 0,
      "label": "datasource",
      "name": "DS_PROMETHEUS",
      "options": [],
      "query": "prometheus",
      "refresh": 1,
      "regex": "",
      "type": "datasource"
    }
  ]
},
```

JSONの仕様については [JSON model | Grafana Labs](https://grafana.com/docs/grafana/latest/dashboards/json-model/) を参考に。

datasources/prometheus.yaml はそのままコピーしただけ。

#### インストール

```bash
$ brew install grafana
```

#### 設定ファイルを配置

設定ファイルの配置先は下記URLを参考にした。

- https://github.com/grafana/grafana/issues/27171
- https://grafana.com/docs/grafana/latest/administration/provisioning/#dashboards

下記のコマンドで `/opt/homebrew/Cellar/grafana/[version]/share/grafana/conf/provisioning/datasources/` 配下に設定ファイルを配置していく。

```bash
# grafana/conf/provisioning/datasources/prometheus.yaml
$ cd /opt/homebrew/Cellar/grafana/[version]/share/grafana/conf/provisioning/datasources
$ ln -s ~/src/github.com/ackintosh/sandbox/lighthouse-metrics/grafana/conf/provisioning/datasources/prometheus.yaml prometheus.yaml

# grafana/conf/provisioning/dashboards
$ cd /opt/homebrew/Cellar/grafana/[version]/share/grafana/conf/provisioning
$ ln -s ~/src/github.com/ackintosh/sandbox/lighthouse-metrics/grafana/conf/provisioning/dashboards dashboards
```

#### 起動、停止

```bash
$ brew services start grafana
$ brew services stop grafana
```

#### 確認

- http://localhost:3000/
- admin/admin
- ダッシュボードの設定をインポートする
  - `Dashboard` -> `Browse` -> `Import` からJSONファイルをアップロードする 
  - 参考: https://github.com/sigp/lighthouse-metrics#usage


## scrape-targets

- そのままコピーしただけ
- prometheus.yml から参照される
- メモ: localhost:5064 は validator client のメトリクス用ポート番号
