# Terraform

## Terraformのバージョン

```bash
$ cat .terraform-version
$ tfenv install
```

## モジュールの使用

### apply

モジュールを使用する場合は、`terraform get` か `terraform init` でモジュールを事前に取得する必要がある。

```bash
$ terraform get
$ terraform apply
```
