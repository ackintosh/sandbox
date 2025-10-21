# 辞書ファイルのzip展開用のコンテナ
FROM alpine:latest AS builder

# サイズが大きいのでコメントアウト
#RUN wget http://sudachi.s3-website-ap-northeast-1.amazonaws.com/sudachidict/sudachi-dictionary-20250515-full.zip
#RUN unzip sudachi-dictionary-20250515-full.zip sudachi-dictionary-20250515/system_full.dic
RUN wget http://sudachi.s3-website-ap-northeast-1.amazonaws.com/sudachidict/sudachi-dictionary-20250515-core.zip
RUN unzip sudachi-dictionary-20250515-core.zip sudachi-dictionary-20250515/system_core.dic
# sudachiがOpenSearch2.19に対応していない
RUN wget --no-check-certificate https://github.com/WorksApplications/elasticsearch-sudachi/releases/download/v3.3.0/opensearch-2.18.0-analysis-sudachi-3.3.0.zip
RUN wget --no-check-certificate https://artifacts.opensearch.org/releases/plugins/analysis-icu/2.18.0/analysis-icu-2.18.0.zip

# opensearchコンテナにコピーする
FROM opensearchproject/opensearch:2.18.0
#COPY --from=builder sudachi-dictionary-20250515/system_full.dic /usr/share/opensearch/tmp/sudachi/
COPY --from=builder sudachi-dictionary-20250515/system_core.dic /usr/share/opensearch/tmp/sudachi/
COPY --from=builder opensearch-2.18.0-analysis-sudachi-3.3.0.zip .
COPY --from=builder analysis-icu-2.18.0.zip .

RUN /usr/share/opensearch/bin/opensearch-plugin install file:opensearch-2.18.0-analysis-sudachi-3.3.0.zip
RUN /usr/share/opensearch/bin/opensearch-plugin install file:analysis-icu-2.18.0.zip
