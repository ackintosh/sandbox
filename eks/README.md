
[Amazon EKS の開始方法 – eksctl]( https://docs.aws.amazon.com/ja_jp/eks/latest/userguide/getting-started-eksctl.html)

```shell
# マネジメントコンソールでEKSのテスト用のユーザを作る
# アタッチするポリシー
# - AmazonVPCFullAccess
# - AWSCloudFormationFullAccess
# - IAMFullAccess
# - インラインポリシー
#   - eks:*

# 作ったユーザのアクセスキー, シークレットアクセスキーを設定する
aws configure
# -> less ~/.aws/credentials

# Amazon EKS クラスターを作成する
eksctl create cluster --name my-cluster --region ap-northeast-1 --fargate
# -> eksctl により、~/.kube 内に kubectl の設定が追加される
grep current-context ~/.kube/config
current-context: eks-tset@my-cluster.ap-northeast-1.eksctl.io

# Kubernetesリソースを表示する
kubectl get nodes -o wide

# クラスタとノードを削除する
eksctl delete cluster --region=ap-northeast-1 --name=my-cluster

```
