///////////////////////////////////////////////////////////////////////
// * 入力パラメータの定義 *
///////////////////////////////////////////////////////////////////////
variable "instance_type" {}

///////////////////////////////////////////////////////////////////////
// * 出力パラメータの定義 *
///////////////////////////////////////////////////////////////////////
output "example_instance_id" {
  // 作成したインスタンスのID
  value = aws_instance.example.id
}
output "example_public_dns" {
  // 作成したインスタンスの公開DNS
  value = aws_instance.example.public_dns
}

///////////////////////////////////////////////////////////////////////
// * リソースの定義 *
///////////////////////////////////////////////////////////////////////
resource "aws_instance" "example" {
  ami = "ami-0c3fd0f5d33134a76"
  // データソースで定義した、最新のAMIを使う場合
  // ami = data.aws_ami.recent_amazon_linux_2

  instance_type = var.instance_type

  // セキュリティグループを追加
  vpc_security_group_ids = [aws_security_group.example_ec2.id]

  // * apacheをインストールする *
  // 外部ファイルを読み込む
  // 引数のパスはterraformコマンドを実行したディレクトリからの相対パス?
  user_data = file("./user_data.sh")

  tags = {
    Name = "abi-01357-example"
  }
}

// セキュリティグループ
resource "aws_security_group" "example_ec2" {
  name = "example-ec2"

  ingress {
    from_port = 80
    protocol = "tcp"
    to_port = 80
    cidr_blocks = ["0.0.0.0/0"]
  }

  egress {
    from_port = 0
    protocol = "-1"
    to_port = 0
    cidr_blocks = ["0.0.0.0/0"]
  }
}


///////////////////////////////////////////////////////////////////////
// * データソースで外部データを参照する *
///////////////////////////////////////////////////////////////////////
//
// 例: 最新のAmazon Linux 2のAMIを定義する
data "aws_ami" "recent_amazon_linux_2" {
  most_recent = true
  owners = ["amazon"]

  filter {
    name = "name"
    values = ["amzn2-ami-hvm-2.0.????????-x86_64-gp2"]
  }

  filter {
    name = "state"
    values = ["available"]
  }
}
