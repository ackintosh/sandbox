FROM docker.elastic.co/elasticsearch/elasticsearch:8.6.2

# sudachiプラグイン
RUN /usr/share/elasticsearch/bin/elasticsearch-plugin install https://github.com/WorksApplications/elasticsearch-sudachi/releases/download/v3.1.0/elasticsearch-8.6.2-analysis-sudachi-3.1.0.zip

# 辞書
COPY ./sudachi-dictionary-20230927-core.zip ./
RUN unzip -o ./sudachi-dictionary-20230927-core.zip && \
  rm ./sudachi-dictionary-20230927-core.zip && \
  mkdir /usr/share/elasticsearch/config/sudachi && \
  mv ./sudachi-dictionary-20230927/system_core.dic /usr/share/elasticsearch/config/sudachi/

