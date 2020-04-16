/////////////////////////////////////////////////////////
// API
/////////////////////////////////////////////////////////
// https://www.terraform.io/docs/providers/aws/r/appsync_graphql_api.html
resource "aws_appsync_graphql_api" "example" {
  authentication_type = "API_KEY"
  name = "example"
  schema = file("./schema.graphqls")
}

output "uri_http" {
  value = aws_appsync_graphql_api.example.uris["GRAPHQL"]
}
output "uri_websocket" {
  value = aws_appsync_graphql_api.example.uris["REALTIME"]
}


/////////////////////////////////////////////////////////
// データソース
/////////////////////////////////////////////////////////
// https://www.terraform.io/docs/providers/aws/r/appsync_datasource.html
resource "aws_appsync_datasource" "example_datasource" {
  api_id = aws_appsync_graphql_api.example.id
  name = "livedoor_weather_api"

  // 外部API
  type = "HTTP"
  http_config {
    endpoint = "http://weather.livedoor.com"
  }
}


/////////////////////////////////////////////////////////
// リゾルバ
/////////////////////////////////////////////////////////
// https://www.terraform.io/docs/providers/aws/r/appsync_resolver.html
resource "aws_appsync_resolver" "example_resolver" {
  api_id = aws_appsync_graphql_api.example.id
  field = "weather"
  type = "Query"

  // データソース
  // * idではなく `name` を指定
  data_source = aws_appsync_datasource.example_datasource.name

  // マッピングテンプレート
  request_template = file("./resolver/request_template.vm")
  response_template = file("./resolver/response_template.vm")

  // キャッシュの設定ができるようにPRを出しているところ
  // https://github.com/terraform-providers/terraform-provider-aws/pull/12747
  // caching_config {
  //   caching_keys = [
  //     "$context.identity.sub",
  //     "$context.arguments.id"
  //   ]
  //   ttl = 120
  // }
}
