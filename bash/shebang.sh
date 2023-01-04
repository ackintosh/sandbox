#!/usr/bin/env bash

# envコマンドを利用する場合
# 例: `#!/usr/bin/env bash`
# $PATH 上の bash が使われる
#
# メリット:
# /opt 配下に bash がインストールされている場合(Homebrew でインストールした場合など)に、
# PATHさえ通っていればそちらが使われる。
# (2023年時点のMacのデフォルトの bash が v3 系で古いので, Homebrewでインストールすることがある)
# ```shell
#     $ /bin/bash --version
#     GNU bash, version 3.2.57(1)-release (arm64-apple-darwin22)
#     Copyright (C) 2007 Free Software Foundation, Inc.
# ```
#

