output "batch_compute_environment_arn" {
  description = "ARN of the Batch compute environment"
  value       = aws_batch_compute_environment.vericoding_compute_env.arn
}

output "batch_job_queue_arn" {
  description = "ARN of the Batch job queue"
  value       = aws_batch_job_queue.vericoding_job_queue.arn
}

output "batch_job_queue_name" {
  description = "Name of the Batch job queue"
  value       = aws_batch_job_queue.vericoding_job_queue.name
}

output "lean_job_definition_arn" {
  description = "ARN of the Lean verification job definition"
  value       = aws_batch_job_definition.lean_verification.arn
}

output "dafny_job_definition_arn" {
  description = "ARN of the Dafny verification job definition"
  value       = aws_batch_job_definition.dafny_verification.arn
}

output "verus_job_definition_arn" {
  description = "ARN of the Verus verification job definition"
  value       = aws_batch_job_definition.verus_verification.arn
}

output "vpc_id" {
  description = "ID of the VPC"
  value       = aws_vpc.batch_vpc.id
}

output "subnet_ids" {
  description = "IDs of the subnets"
  value       = aws_subnet.batch_subnet[*].id
}

output "security_group_id" {
  description = "ID of the security group"
  value       = aws_security_group.batch_sg.id
}