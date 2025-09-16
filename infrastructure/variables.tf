variable "aws_region" {
  description = "AWS region for resources"
  type        = string
  default     = "us-west-2"
}

variable "max_vcpus" {
  description = "Maximum vCPUs for the compute environment"
  type        = number
  default     = 80  # 10 machines * 8 vCPUs each
}


variable "project_name" {
  description = "Name of the project"
  type        = string
  default     = "vericoding"
}