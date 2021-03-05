# gotrace

https://github.com/divan/gotrace/issues/20#issuecomment-394171327


```fish
##############################################################################
# go 1.8対応版のgotraceをダウンロードする
##############################################################################
ghq get https://github.com/divan/gotrace.git
gco go18


##############################################################################
# 依存パッケージをダウンロードする
##############################################################################
# https://github.com/divan/gotrace/pull/22
cp ./go.mod /Users/abi01357/src/github.com/divan/gotrace/
cp ./go.sum /Users/abi01357/src/github.com/divan/gotrace/

# go.mod にかかれている依存パッケージをダウンロードするためにgo buildを実行する
go build


##############################################################################
# go.modで `pkg` 配下にインストールされた依存パッケージを $GOPATH 配下にコピーする
# ※ $GOPATH -> ホームディレクトリ
##############################################################################
# elazarl/go-bindata-assetfs
mkdir -p ~/src/github.com/elazarl/go-bindata-assetfs
cp -r ~/go/pkg/mod/github.com/elazarl/go-bindata-assetfs@v1.0.0/* ~/src/github.com/elazarl/go-bindata-assetfs/

# golang.org tools
mkdir -p ~/src/golang.org/x/tools/
cp -r ~/go/pkg/mod/golang.org/x/tools@v0.0.0-20190525145741-7be61e1b0e51/* ~/src/golang.org/x/tools/


##############################################################################
# gotraceをビルドする
##############################################################################
docker run -v $GOPATH:/go -w /go/src/github.com/divan/gotrace golang:1.8 go install


##############################################################################
# gotraceを実行する
##############################################################################
docker run -p 2000:2000 -v $GOPATH:/go -v $PWD:/go/src/app -w /go/src/app golang:1.8 gotrace examples/pingpong02.go
```
