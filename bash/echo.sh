#!/bin/bash
set -euo pipefail

# -n オプション
echo -n "改行なし..."
echo " ...Done"

# -e オプション
echo "デフォルトではバックスラッシュをエスケープする\n"
echo -e "-eオプションでエスケープを無効化する\n"


