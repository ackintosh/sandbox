#!/bin/bash

# Dockerfileで/usr/share/opensearch/config/sudachi/にCOPYすると、
# compose.yamlで定義しているマウント定義で上書きされてしまうため、DockerfileでtmpにCOPYしたものを更にここでcpしている
cp -r /usr/share/opensearch/tmp/sudachi/. /usr/share/opensearch/config/sudachi/

./opensearch-docker-entrypoint.sh
