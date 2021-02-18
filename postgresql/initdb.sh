#!/bin/bash

set -Eeuo pipefail

for db in $(echo $POSTGRES_MULTIPLE_DATABASES | tr ',' ' '); do
  echo "Creating my_schema schema for $db"
  echo "CREATE SCHEMA my_schema;" | psql --username "$POSTGRES_USER" $db -f -
done
