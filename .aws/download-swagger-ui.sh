#!/bin/bash
set -e

curl -O -L https://github.com/swagger-api/swagger-ui/archive/v3.37.0.tar.gz
tar -xvf v3.37.0.tar.gz
mv swagger-ui-3.37.0/dist ./swagger-ui
