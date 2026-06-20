#!/usr/bin/env bash
set -euo pipefail

for dir in ./*/; do
  # ディレクトリでない場合はスキップ
  [ -d "$dir" ] || continue

  # Cargo.toml があれば cargo project とみなす
  if [ -f "${dir}Cargo.toml" ]; then
    echo "Running cargo clean in ${dir}"
    (
      cd "$dir"
      cargo clean
    )
  fi
done
