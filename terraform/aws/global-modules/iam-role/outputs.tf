output "iam_role_arn" {
  description = "iam_role arn"
  value       = aws_iam_role.default.arn
}

output "iam_role_name" {
  description = "iam_role name"
  value       = aws_iam_role.default.name
}
