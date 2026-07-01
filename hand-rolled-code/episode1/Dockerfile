FROM php:8.5-apache

RUN pecl install redis && docker-php-ext-enable redis

RUN apt-get update && apt-get install -y libmemcached-dev zlib1g-dev \
    && pecl install memcached \
    && docker-php-ext-enable memcached \
    && rm -rf /var/lib/apt/lists/*
