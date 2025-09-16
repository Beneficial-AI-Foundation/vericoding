terraform {
  required_version = ">= 1.0"
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }
  }
}

provider "aws" {
  region = "eu-west-2"
}

# VPC and networking
resource "aws_vpc" "batch_vpc" {
  cidr_block           = "10.0.0.0/16"
  enable_dns_hostnames = true
  enable_dns_support   = true
  
  tags = {
    Name = "vericoding-batch-vpc"
  }
}

resource "aws_internet_gateway" "batch_igw" {
  vpc_id = aws_vpc.batch_vpc.id
  
  tags = {
    Name = "vericoding-batch-igw"
  }
}

resource "aws_subnet" "batch_subnet" {
  count = 2
  
  vpc_id                  = aws_vpc.batch_vpc.id
  cidr_block              = "10.0.${count.index + 1}.0/24"
  availability_zone       = data.aws_availability_zones.available.names[count.index]
  map_public_ip_on_launch = true
  
  tags = {
    Name = "vericoding-batch-subnet-${count.index + 1}"
  }
}

resource "aws_route_table" "batch_rt" {
  vpc_id = aws_vpc.batch_vpc.id
  
  route {
    cidr_block = "0.0.0.0/0"
    gateway_id = aws_internet_gateway.batch_igw.id
  }
  
  tags = {
    Name = "vericoding-batch-rt"
  }
}

resource "aws_route_table_association" "batch_rta" {
  count = 2
  
  subnet_id      = aws_subnet.batch_subnet[count.index].id
  route_table_id = aws_route_table.batch_rt.id
}

# Security Group
resource "aws_security_group" "batch_sg" {
  name_prefix = "vericoding-batch-"
  vpc_id      = aws_vpc.batch_vpc.id
  
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  tags = {
    Name = "vericoding-batch-sg"
  }
}

# IAM Role for Batch Service
resource "aws_iam_role" "batch_service_role" {
  name = "vericoding-batch-service-role"
  
  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Action = "sts:AssumeRole"
        Effect = "Allow"
        Principal = {
          Service = "batch.amazonaws.com"
        }
      }
    ]
  })
}

resource "aws_iam_role_policy_attachment" "batch_service_role_policy" {
  role       = aws_iam_role.batch_service_role.name
  policy_arn = "arn:aws:iam::aws:policy/service-role/AWSBatchServiceRole"
}

# IAM Role for EC2 instances
resource "aws_iam_role" "batch_instance_role" {
  name = "vericoding-batch-instance-role"
  
  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Action = "sts:AssumeRole"
        Effect = "Allow"
        Principal = {
          Service = "ec2.amazonaws.com"
        }
      }
    ]
  })
}

resource "aws_iam_role_policy_attachment" "batch_instance_role_policy" {
  role       = aws_iam_role.batch_instance_role.name
  policy_arn = "arn:aws:iam::aws:policy/service-role/AmazonEC2ContainerServiceforEC2Role"
}

# Additional policy for accessing Parameter Store
resource "aws_iam_role_policy" "batch_job_ssm_policy" {
  name = "vericoding-batch-job-ssm-policy"
  role = aws_iam_role.batch_job_role.id
  
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Effect = "Allow"
        Action = [
          "ssm:GetParameter",
          "ssm:GetParameters",
          "ssm:GetParametersByPath"
        ]
        Resource = [
          "arn:aws:ssm:eu-west-2:${data.aws_caller_identity.current.account_id}:parameter/vericoding/*"
        ]
      }
    ]
  })
}

resource "aws_iam_instance_profile" "batch_instance_profile" {
  name = "vericoding-batch-instance-profile"
  role = aws_iam_role.batch_instance_role.name
}

# IAM Role for Spot Fleet
resource "aws_iam_role" "batch_spot_fleet_role" {
  name = "vericoding-batch-spot-fleet-role"
  
  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Action = "sts:AssumeRole"
        Effect = "Allow"
        Principal = {
          Service = "spotfleet.amazonaws.com"
        }
      }
    ]
  })
}

resource "aws_iam_role_policy_attachment" "batch_spot_fleet_policy" {
  role       = aws_iam_role.batch_spot_fleet_role.name
  policy_arn = "arn:aws:iam::aws:policy/service-role/AmazonEC2SpotFleetTaggingRole"
}

# Compute Environment
resource "aws_batch_compute_environment" "vericoding_compute_env" {
  compute_environment_name = "vericoding-compute-env"
  type                    = "MANAGED"
  state                   = "ENABLED"
  service_role            = aws_iam_role.batch_service_role.arn
  
  compute_resources {
    type                = "EC2"
    allocation_strategy = "SPOT_CAPACITY_OPTIMIZED"
    
    min_vcpus     = 0    # Scale to 0 when idle
    max_vcpus     = 80   # 10 machines * 8 vCPUs each
    desired_vcpus = 0    # Target 0 instances
    
    instance_type = "c8g.2xlarge"
    
    spot_fleet_request_role = aws_iam_role.batch_spot_fleet_role.arn
    bid_percentage             = 100  # 100% of on-demand price
    
    ec2_configuration {
      image_type = "ECS_AL2_ARM64"  # ARM64 for Graviton3
    }
    
    instance_role = aws_iam_instance_profile.batch_instance_profile.arn
    
    subnets         = aws_subnet.batch_subnet[*].id
    security_group_ids = [aws_security_group.batch_sg.id]
    
    tags = {
      Name        = "vericoding-batch-instance"
      Environment = "development"
      Project     = "vericoding"
    }
  }
  
  depends_on = [
    aws_iam_role_policy_attachment.batch_service_role_policy
  ]
}

# Job Queue
resource "aws_batch_job_queue" "vericoding_job_queue" {
  name                 = "vericoding-job-queue"
  state                = "ENABLED"
  priority             = 1
  compute_environments = [aws_batch_compute_environment.vericoding_compute_env.arn]
  
  depends_on = [aws_batch_compute_environment.vericoding_compute_env]
}

# Job Definition for Lean verification
resource "aws_batch_job_definition" "lean_verification" {
  name = "lean-verification"
  type = "container"
  
  platform_capabilities = ["EC2"]
  
  container_properties = jsonencode({
    image = "ubuntu:22.04"
    vcpus = 8
    memory = 15360  # 15GB (leave 1GB for system)
    
    jobRoleArn = aws_iam_role.batch_job_role.arn
    
    environment = [
      {
        name  = "DEBIAN_FRONTEND"
        value = "noninteractive"
      },
      {
        name  = "WORKSPACE"
        value = "/workspace"
      }
    ]
    
    secrets = [
      {
        name      = "OPENAI_API_KEY"
        valueFrom = "arn:aws:ssm:eu-west-2:${data.aws_caller_identity.current.account_id}:parameter/vericoding/openai-api-key"
      },
      {
        name      = "WANDB_API_KEY" 
        valueFrom = "arn:aws:ssm:eu-west-2:${data.aws_caller_identity.current.account_id}:parameter/vericoding/wandb-api-key"
      }
    ]
    
    mountPoints = []
    volumes     = []
    
    ulimits = []
  })
  
  retry_strategy {
    attempts = 2
  }
}


# IAM Role for Job execution
resource "aws_iam_role" "batch_job_role" {
  name = "vericoding-batch-job-role"
  
  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Action = "sts:AssumeRole"
        Effect = "Allow"
        Principal = {
          Service = "ecs-tasks.amazonaws.com"
        }
      }
    ]
  })
}

# Data sources
data "aws_availability_zones" "available" {
  state = "available"
}

data "aws_caller_identity" "current" {}