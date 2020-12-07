locals {
  codepipeline_name = "test_codepipeline_name"
  codebuild_name = "test_codebuild_name"
}

provider "aws" {
  region = "ap-northeast-1"
}

terraform {
  # https://github.com/hashicorp/terraform/releases
  required_version = "0.13.5"

  required_providers {
    # https://github.com/terraform-providers/terraform-provider-aws/releases
    aws = "3.18.0"
  }
}

############################################################################
# ポリシー
############################################################################
data "aws_iam_policy_document" "codepipeline_policy" {
  # CodePipelineアーティファクト用のS3バケットへ読み書きする権限
  statement {
    effect = "Allow"
    actions = [
      "s3:GetObject",
      "s3:GetObjectVersion",
      "s3:GetBucketVersioning",
      "s3:PutObject",
    ]
    resources = [
      module.s3_bucket_for_codepipeline_artifact.this_s3_bucket_arn,
      "${module.s3_bucket_for_codepipeline_artifact.this_s3_bucket_arn}/*",
    ]
  }

  # CodeBuildを起動する権限
  # 権限リファレンス:https://docs.aws.amazon.com/ja_jp/codebuild/latest/userguide/auth-and-access-control-permissions-reference.html
  statement {
    effect = "Allow"
    actions = [
      "codebuild:BatchGetBuilds",
      "codebuild:StartBuild",
    ]
    resources = [
      aws_codebuild_project.test_codebuild.arn
    ]
  }
}

data "aws_iam_policy_document" "codebuild_policy" {
  # CodePipelineアーティファクト用のS3オブジェクトへ読み書きする権限
  statement {
    effect = "Allow"
    actions = [
      "s3:GetObject",
      "s3:GetObjectVersion",
      "s3:GetBucketVersioning",
      "s3:PutObject",
    ]
    resources = [
      module.s3_bucket_for_codepipeline_artifact.this_s3_bucket_arn,
      "${module.s3_bucket_for_codepipeline_artifact.this_s3_bucket_arn}/*",
    ]
  }
}

############################################################################
# ロール
############################################################################
# CodePipelineロール
module "codepipeline_role" {
  source     = "../global-modules/iam-role"
  name       = "test-codepipeline-role"
  policy     = data.aws_iam_policy_document.codepipeline_policy.json
  identifier = "codepipeline.amazonaws.com"
}

# CodeBuildロール
module "codebuild_role" {
  source     = "../global-modules/iam-role"
  name       = "test-codebuild-role"
  identifier = "codebuild.amazonaws.com"
  policy     = data.aws_iam_policy_document.codebuild_policy.json
}

############################################################################
# CodeBuild
############################################################################
resource "aws_codebuild_project" "test_codebuild" {
  name = local.codebuild_name

  service_role = module.codebuild_role.iam_role_arn

  artifacts {
    type = "CODEPIPELINE"
  }

  source {
    type      = "CODEPIPELINE"
    buildspec = ".aws/buildspec.yaml"
  }

  cache {
    type = "NO_CACHE"
  }

  environment {
    # https://docs.aws.amazon.com/ja_jp/codebuild/latest/userguide/build-env-ref-available.html
    image        = "aws/codebuild/amazonlinux2-x86_64-standard:3.0"
    type         = "LINUX_CONTAINER"
    compute_type = "BUILD_GENERAL1_SMALL"
  }
}


############################################################################
# CodePipeline
############################################################################
# https://docs.aws.amazon.com/ja_jp/codepipeline/latest/userguide/reference-pipeline-structure.html
resource "aws_codepipeline" "test_codepipeline" {
  name = local.codepipeline_name

  role_arn = module.codepipeline_role.iam_role_arn

  # stage間でデータを共有するためのバケット
  artifact_store {
    type     = "S3"
    location = module.s3_bucket_for_codepipeline_artifact.this_s3_bucket_id
  }

  # GitHubからソースコードを取得する
  stage {
    name = "Source"

    action {
      name             = "Source"
      category         = "Source"
      owner            = "ThirdParty"
      provider         = "GitHub"
      version          = "1"
      run_order        = 1
      output_artifacts = ["Source"]

      configuration = {
        Owner      = "ackintosh"
        Repo       = "sandbox"
        Branch     = "master"
        OAuthToken = "dummy"
        # GitHubからのWebHookでCodePipelineを起動させるので、CodePipelineからGitHubをポーリングする処理は無効にする
        PollForSourceChanges = false
      }
    }
  }

  ##################
  # Build
  ##################
  stage {
    name = "Build"

    action {
      name             = "Build"
      category         = "Build"
      owner            = "AWS"
      provider         = "CodeBuild"
      version          = "1"
      run_order        = 1
      input_artifacts  = ["Source"]
      output_artifacts = ["Build"]

      configuration = {
        ProjectName = aws_codebuild_project.test_codebuild.name
      }
    }
  }

  ##################
  # Deployは省略
  ##################

  depends_on = [
    aws_codebuild_project.test_codebuild,
  ]

  lifecycle {
    ignore_changes = [
      # GitHubの接続設定はCodePipeline上で上書きする
      stage[0].action[0].configuration,
    ]
  }
}

# CodePipelineのステージ間でデータを共有するためのバケット
module "s3_bucket_for_codepipeline_artifact" {
  # https://registry.terraform.io/modules/terraform-aws-modules/s3-bucket/aws/
  source  = "terraform-aws-modules/s3-bucket/aws"
  version = "~> 1.12"

  bucket = "test-bucket-for-codepipeline-artifact"

  server_side_encryption_configuration = {
    rule = {
      # SSE-S3で暗号化
      apply_server_side_encryption_by_default = {
        sse_algorithm = "AES256"
      }
    }
  }

  lifecycle_rule = [
    {
      enabled = true
      expiration = {
        days = 7
      }
    },
  ]

  block_public_acls       = true
  block_public_policy     = true
  ignore_public_acls      = true
  restrict_public_buckets = true
}

resource "aws_codepipeline_webhook" "this" {
  name            = "sandbox-codepipeline-webhook"
  target_pipeline = aws_codepipeline.test_codepipeline.name
  target_action   = "Source"
  authentication  = "GITHUB_HMAC"

  authentication_configuration {
    secret_token = "dummy"
  }

  filter {
    json_path = "$.ref"
    match_equals = "refs/heads/{Branch}"
  }

  lifecycle {
    ignore_changes = [
      authentication_configuration
    ]
  }
}
