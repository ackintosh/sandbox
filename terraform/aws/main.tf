///////////////////////////////////////////////////////////////////////
// * リソースの定義 *
///////////////////////////////////////////////////////////////////////
// EC2
module "web_server" {
  source = "./modules/http_server"
  // モジュールの入力パラメータ `instance_type` を指定
  instance_type = local.example_instance_type // ローカル変数を使用
}

///////////////////////////////////////////////////////////////////////
// * 変数の定義 *
///////////////////////////////////////////////////////////////////////
// 実行時に上書きするコマンド例
// $ terraform plan -var 'example_instance_type=t3.nano'
// 環境変数で上書きする場合は `TF_VAR_<name>` で指定する
// $ TF_VAR_example_instance_type=t3.nano terraform plan
variable "example_instance_type" {
  default = "t2.micro"
}

///////////////////////////////////////////////////////////////////////
// * ローカル変数の定義 *
///////////////////////////////////////////////////////////////////////
locals {
  example_instance_type = "t2.micro"
}


///////////////////////////////////////////////////////////////////////
// * 出力値の定義 *
///////////////////////////////////////////////////////////////////////
//
// apply時にターミナルに値を出力する
// https://www.terraform.io/docs/configuration/outputs.html
//
// (出力例)
// =================================================
// Outputs:
//
// example_instance_id = i-xxxxxxxxxxxxxxxxx
// example_public_dns = ec2-xxx-xxx-xxx-xxx.ap-northeast-1.compute.amazonaws.com
// =================================================
// 作成されたEC2インスタンスIDを出力
output "instance_id" {
  // web_serverモジュールの出力パラメータを使用する
  value = module.web_server.example_instance_id
}
// 作成されたEC2インスタンスの公開DNSを出力
output "public_dns" {
  // web_serverモジュールの出力パラメータを使用する
  value = module.web_server.example_public_dns
}


///////////////////////////////////////////////////////////////////////
// * プロバイダの定義 *
///////////////////////////////////////////////////////////////////////
// 省略してもTerraformが暗黙的に検出してくれる
provider "aws" {
  region = "ap-northeast-1"
}
