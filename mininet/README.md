# Get started with mininet

http://mininet.org/download/

# Walkthrough

http://mininet.org/walkthrough/#part-1-everyday-mininet-usage

## VMware Fusion

Ubuntuをインストール

https://dev.to/daud99/installing-ubuntu-using-vmware-fusion-tech-preview-on-mac-m1-silicon-4b0e

UbuntuでMininetをセットアップ

http://mininet.org/download/

他、Scrapboxの ubuntu と Mininet を参照

## Pythonスクリプトの実行

```bash
# VMで実行する
sudo python3 simple.py
```

---

## Memo:VirtualBoxはイメージが起動できなかったので諦めた

M1 Mac用のVirtualBoxがdeveloper previewだからかもしれない。

- VirtualBox: https://www.virtualbox.org/wiki/Downloads
- Mininet VM image: https://github.com/mininet/mininet/releases/

http://mininet.org/vm-setup-notes/

##### Host-only Networkを作成する

- ファイル -> ツール -> Network Manager
- Host-only Networksタブで「作成」

<img width="1396" alt="image" src="https://user-images.githubusercontent.com/1885716/206936342-5e2d7bb5-81b5-4933-b03e-c99e1a9345a0.png">


#### VM設定でHost-only networkを追加する

- VMを選択 -> 設定 -> ネットワーク

<img width="1413" alt="image" src="https://user-images.githubusercontent.com/1885716/206936308-20be05e9-21ca-4934-b9c4-2df15f78e881.png">


## Memo: Dockerは諦めた

macOSでMininetのWalkthrough(http://mininet.org/walkthrough/)をすすめようとして  
Dockerfileを作っていたが、wiresharkが起動できない（GUIがない）ので諦めた。

```
docker build -t mininet .
docker run --rm -it mininet
```
