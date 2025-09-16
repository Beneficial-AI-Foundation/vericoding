variable "aws_region" {
  description = "AWS region for resources"
  type        = string
  default     = "us-west-2"
}

variable "max_vcpus" {
  description = "Maximum vCPUs for the compute environment"
  type        = number
  default     = 1000
}

variable "job_timeout_seconds" {
  description = "Default job timeout in seconds"
  type        = number
  default     = 3600  # 1 hour
}

variable "project_name" {
  description = "Name of the project"
  type        = string
  default     = "vericoding"
}