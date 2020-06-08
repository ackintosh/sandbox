# SonarQube

### SonarQube Serverの起動

```shell
docker-compose up
open localhost:9000

# admin/adminでログイン
```

### 解析

##### SonarQube Gradleプラグイン

- [SonarScanner for Gradle | SonarQube Docs](https://docs.sonarqube.org/latest/analysis/scan/sonarscanner-for-gradle/)
- [Gradle - Plugin: org.sonarqube](https://plugins.gradle.org/plugin/org.sonarqube)

build.graldeの設定と、gradle.properties の設定が必要。

```
# gradle.properties
systemProp.sonar.host.url=http://localhost:9000
 
#----- Token generated from an account with 'publish analysis' permission
systemProp.sonar.login=<token>
```

##### SonarScanner CLI

https://github.com/SonarSource/sonar-scanner-cli-docker

解析対象のディレクトリに [sonar-project.properties](https://docs.sonarqube.org/latest/analysis/scan/sonarscanner/#header-2) を作っておく。  

```shell
# カレントディレクトリのソースコードを解析する (fish用)
docker run --network=sonarqube_default -e SONAR_HOST_URL=http://sonarqube:9000 -it -v (pwd):/usr/src sonarsource/sonar-scanner-cli

# ネットワーク名は `docker network ls` で確認する
# だいたいは `sonarqube_default (ディレクトリ名_default)` のはず
```

## 参考URL
- [SonerQubeを使ったGoプロジェクトの品質管理 - Qiita](https://qiita.com/nanamen/items/37ac8b05fdf5af7c239f)
  - Compose v3用に修正した (`volumes_from` の廃止)
