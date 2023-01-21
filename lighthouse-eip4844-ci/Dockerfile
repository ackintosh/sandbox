# CI の `build-docker-single-arch` ジョブを再現する Dockerfile
# https://github.com/sigp/lighthouse/blob/d96d793bfbbef2322cba99b1676c3d63e1197b15/.github/workflows/docker.yml#L57

# docker build . -t eip4844
# docker run -it --rm -v (pwd)/lighthouse:/lighthouse eip4844

FROM ubuntu:22.04

#    DOCKER_PASSWORD: ***
#    DOCKER_USERNAME: ***
#    IMAGE_NAME: sigp/lighthouse
#    LCLI_IMAGE_NAME: sigp/lcli
#    DOCKER_CLI_EXPERIMENTAL: enabled
#    VERSION: eip4844
#    VERSION_SUFFIX: 
#    CROSS_FEATURES: 

# デフォルトは /bin/sh で、これだと source コマンドが見つからず都合が悪いので bash に変更
SHELL ["/bin/bash", "-c"]

RUN set -ex \
  && apt-get update \
  && apt-get install -y curl \
  # build-essential をインストールしないと
  # linker `cc` not found
  # というエラーが出る
  && apt-get install -y build-essential \
  # Rustのインストール
  && curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup.sh \
  && chmod 755 rustup.sh \
  && ./rustup.sh -y \
  # PATHを通す
  && source "$HOME/.cargo/env" \
  # crossのインストール
  && cargo install cross

# ubuntu に Docker をインストールする
# https://docs.docker.com/engine/install/ubuntu/
RUN set -ex \
  && apt-get install -y ca-certificates gnupg lsb-release \
  && mkdir -p /etc/apt/keyrings \
  && curl -fsSL https://download.docker.com/linux/ubuntu/gpg | gpg --dearmor -o /etc/apt/keyrings/docker.gpg \
  && echo "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/docker.gpg] https://download.docker.com/linux/ubuntu $(lsb_release -cs) stable" | tee /etc/apt/sources.list.d/docker.list > /dev/null \
  && apt-get update \
  && apt-get install -y docker-ce docker-ce-cli

