# チュートリアル: Amazon Kinesis で AWS Lambda を使用する
# https://docs.aws.amazon.com/ja_jp/lambda/latest/dg/with-kinesis-example.html
# Amazon Kinesis で AWS Lambda を使用する
# https://docs.aws.amazon.com/ja_jp/lambda/latest/dg/with-kinesis.html

# #############################################################################
# Lambda実行ロール
# https://docs.aws.amazon.com/ja_jp/lambda/latest/dg/lambda-intro-execution-role.html
# #############################################################################
resource "aws_iam_role" "default" {
  name               = "lambda-kinesis-role"
  assume_role_policy = data.aws_iam_policy_document.assume_role.json
}

data "aws_iam_policy_document" "assume_role" {
  statement {
    actions = ["sts:AssumeRole"]
    principals {
      type        = "Service"
      identifiers = ["lambda.amazonaws.com"]
    }
  }
}

resource "aws_iam_policy" "default" {
  name   = "lambda-kinesis-role"
  policy = data.aws_iam_policy_document.lambda_sandbox.json
}

data "aws_iam_policy_document" "lambda_sandbox" {
  statement {
    # https://docs.aws.amazon.com/ja_jp/lambda/latest/dg/with-kinesis.html#events-kinesis-permissions
    actions = [
      "kinesis:DescribeStream",
      "kinesis:DescribeStreamSummary",
      "kinesis:GetRecords",
      "kinesis:GetShardIterator",
      "kinesis:ListShards",
      "kinesis:ListStreams",
      "kinesis:SubscribeToShard",
    ]
    effect = "Allow"
    resources = [
      "*"
    ]
  }

  statement {
    actions = [
      "logs:CreateLogStream",
      "logs:PutLogEvents",
    ]
    effect = "Allow"
    resources = [
      "*"
    ]
  }
}

resource "aws_iam_role_policy_attachment" "default" {
  role       = aws_iam_role.default.name
  policy_arn = aws_iam_policy.default.arn
}

# #############################################################################
# Lambda関数
# #############################################################################
resource "aws_lambda_function" "this" {
  filename      = data.archive_file.src.output_path
  function_name = "lambda-triggered-by-kinesis-data-stream"

  role             = aws_iam_role.default.arn
  handler          = "sandbox"
  source_code_hash = data.archive_file.src.output_base64sha256
  runtime          = "go1.x"
  timeout          = 60 * 5 # 5分
}

data "archive_file" "src" {
  type        = "zip"
  source_file = "cmd/sandbox/sandbox"
  output_path = "cmd/sandbox/sandbox.zip"
}

resource "aws_cloudwatch_log_group" "this" {
  name              = "/aws/lambda/lambda-triggered-by-kinesis-data-stream"
  retention_in_days = 3
}

# Lambda関数を Kinesis Data Stream にマップする
resource "aws_lambda_event_source_mapping" "example" {
  event_source_arn  = aws_kinesis_stream.this.arn
  function_name     = aws_lambda_function.this.arn
  starting_position = "LATEST"
  depends_on = [aws_kinesis_stream.this, aws_lambda_function.this]
}

# #############################################################################
# Kinesis Data Stream
# #############################################################################
resource "aws_kinesis_stream" "this" {
  name        = "sandbox-stream"
  shard_count = 1

  # 単位:時間
  retention_period = 24

  encryption_type = "NONE"
}
