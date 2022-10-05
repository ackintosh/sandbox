provider "aws" {
  region = "ap-northeast-1"
}
 
terraform {
  # https://github.com/hashicorp/terraform/releases
  required_version = "1.3.1"
 
  required_providers {
    # https://github.com/terraform-providers/terraform-provider-aws/releases
    aws = "4.33.0"
  }
}
