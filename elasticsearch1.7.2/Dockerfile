FROM openjdk:8-slim

# *** Elasticsearch 1.7.2 ***
#
# This file is based on:
# https://github.com/docker-library/elasticsearch/blob/aadd13a371dc4226eba7409c59b9d6cffb227f78/1.7/Dockerfile
# 
# An official elasticsearch:1.7.2 image is here:
# https://hub.docker.com/layers/library/elasticsearch/1.7.2/images/sha256-038a4d0b40feff96d5babea8d4f1dc4bd2d9f9d798bb168aeced84180291c3eb?context=explore
#
# However, the official image is too old, so you might encounter an error when pulling the image due to the image format:
# https://docs.docker.com/engine/deprecated/#pushing-and-pulling-with-image-manifest-v2-schema-1
#
# That's why I created this file.

RUN groupadd -r elasticsearch && useradd -r -g elasticsearch elasticsearch

RUN apt-get update \
  && apt-get install  -y --no-install-recommends gosu \
  && apt-get install  -y --no-install-recommends wget \
  && rm -rf /var/lib/apt/lists/*

# ref: https://www.elastic.co/guide/en/elasticsearch/reference/current/deb.html#install-deb
RUN wget https://download.elastic.co/elasticsearch/elasticsearch/elasticsearch-1.7.2.deb \
  && wget https://download.elastic.co/elasticsearch/elasticsearch/elasticsearch-1.7.2.deb.sha1.txt \
  && SHA1_HASH=$(cat elasticsearch-1.7.2.deb.sha1.txt) \
  sha1sum elasticsearch-1.7.2.deb | awk '{print $1}' | grep -q "$SHA1_HASH" && echo "SHA1 matches" || exit 1
RUN dpkg -i elasticsearch-1.7.2.deb

ENV PATH /usr/share/elasticsearch/bin:$PATH

RUN set -ex \
	&& for path in \
		/usr/share/elasticsearch/data \
		/usr/share/elasticsearch/logs \
		/usr/share/elasticsearch/config \
		/usr/share/elasticsearch/config/scripts \
	; do \
		mkdir -p "$path"; \
		chown -R elasticsearch:elasticsearch "$path"; \
	done

COPY config/logging.yml /usr/share/elasticsearch/config/

VOLUME /usr/share/elasticsearch/data

COPY docker-entrypoint.sh /

ENTRYPOINT ["/docker-entrypoint.sh"]

EXPOSE 9200 9300

CMD ["elasticsearch"]
