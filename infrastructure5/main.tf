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

# Data source for Ubuntu AMI
data "aws_ami" "ubuntu" {
  most_recent = true
  owners      = ["099720109477"] # Canonical

  filter {
    name   = "name"
    values = ["ubuntu/images/hvm-ssd/ubuntu-jammy-22.04-amd64-server-*"]
  }

  filter {
    name   = "virtualization-type"
    values = ["hvm"]
  }
}

# Data source for availability zones
data "aws_availability_zones" "available" {
  state = "available"
}

# VPC
resource "aws_vpc" "intern_vpc" {
  cidr_block           = "10.1.0.0/16"
  enable_dns_hostnames = true
  enable_dns_support   = true
  
  tags = {
    Name = "intern-vpc"
  }
}

# Internet Gateway
resource "aws_internet_gateway" "intern_igw" {
  vpc_id = aws_vpc.intern_vpc.id
  
  tags = {
    Name = "intern-igw"
  }
}

# Subnet
resource "aws_subnet" "intern_subnet" {
  vpc_id                  = aws_vpc.intern_vpc.id
  cidr_block              = "10.1.1.0/24"
  availability_zone       = data.aws_availability_zones.available.names[0]
  map_public_ip_on_launch = true
  
  tags = {
    Name = "intern-subnet"
  }
}

# Route Table
resource "aws_route_table" "intern_rt" {
  vpc_id = aws_vpc.intern_vpc.id
  
  route {
    cidr_block = "0.0.0.0/0"
    gateway_id = aws_internet_gateway.intern_igw.id
  }
  
  tags = {
    Name = "intern-rt"
  }
}

# Route Table Association
resource "aws_route_table_association" "intern_rta" {
  subnet_id      = aws_subnet.intern_subnet.id
  route_table_id = aws_route_table.intern_rt.id
}

# Security Group - Basic SSH and HTTP(S) access
resource "aws_security_group" "intern_sg" {
  name_prefix = "intern-sg-"
  vpc_id      = aws_vpc.intern_vpc.id
  
  # SSH access
  ingress {
    from_port   = 22
    to_port     = 22
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  # HTTP access
  ingress {
    from_port   = 80
    to_port     = 80
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  # HTTPS access
  ingress {
    from_port   = 443
    to_port     = 443
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  # All outbound traffic
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  tags = {
    Name = "intern-sg"
  }
}

# Minimal IAM Role for EC2 - No sensitive permissions
resource "aws_iam_role" "intern_ec2_role" {
  name = "intern-ec2-role"
  
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
  
  tags = {
    Name = "intern-ec2-role"
  }
}

# Minimal policy - only basic EC2 metadata access
resource "aws_iam_role_policy" "intern_minimal_policy" {
  name = "intern-minimal-policy"
  role = aws_iam_role.intern_ec2_role.id
  
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Effect = "Allow"
        Action = [
          "ec2:DescribeInstances",
          "ec2:DescribeInstanceTypes"
        ]
        Resource = "*"
      }
    ]
  })
}

# Instance Profile for the role
resource "aws_iam_instance_profile" "intern_instance_profile" {
  name = "intern-instance-profile"
  role = aws_iam_role.intern_ec2_role.name
}

# EC2 Instance
resource "aws_instance" "intern_server" {
  ami           = data.aws_ami.ubuntu.id
  instance_type = "c7a.2xlarge"
  
  subnet_id              = aws_subnet.intern_subnet.id
  vpc_security_group_ids = [aws_security_group.intern_sg.id]
  iam_instance_profile   = aws_iam_instance_profile.intern_instance_profile.name
  
  root_block_device {
    volume_size = 100
    volume_type = "gp3"
  }
  
  user_data = <<-EOF
    #!/bin/bash
    apt-get update
    apt-get install -y build-essential git curl
    
    # Add Theo's SSH public key to ubuntu user
    mkdir -p /home/ubuntu/.ssh
    echo "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABgQC4IgPSH5Kkxy80bIHMjAEN6XovrP2NG/4ccZs8j8Ebdpe3rsE6CmLWohtbKGX6i8yJwQ5jCrrmKmnfx6feOkYaiUY2WLXQQR3hZ4j6GfN52LFzIXnwU84vf0YGSGbhWkrYFRHI16ccYn2IZhSTdxgHvgOehflr2VW7I60y6F8rNNJyfoYHTB/H0zQsoBlLcCLMrEbb5/KpOTIy6B+mn/5+fe74a9YNNJWnslqWI7AHMMzWx8UNzE+3kAY8zuApFe9FXnZNwL05N4l+Y8IzWMaZd7PGg6AUt2BLjx6bGJg8Ob3GogY/nMHxw05xMvYhD4lOz+jqjSUFJ6zQ9C3gWO2OwcIAiXS4kr/LIqwPIRNDxqFUFtU6CWMpUIJ323Yok0nMNwIylMoESFRwOqIFdt66kZyNCGRRAYEJKhp8j9Uqm9P3EncJDFvaw7X4hOYIk1hGWVFfOIfeKAYkIc9F7Qn6x45pYNiFaIj1nn4gamlCGYroAlzrRMLnmHN7YIynrw0= theo@lutfisk" >> /home/ubuntu/.ssh/authorized_keys
    chown ubuntu:ubuntu /home/ubuntu/.ssh/authorized_keys
    chmod 600 /home/ubuntu/.ssh/authorized_keys
    
    echo "Server setup complete" > /var/log/user-data.log
  EOF
  
  tags = {
    Name = "intern-server"
    Purpose = "intern-development"
  }
}

# Output the public IP
output "intern_server_public_ip" {
  value = aws_instance.intern_server.public_ip
}

# Output SSH connection command
output "ssh_connection" {
  value = "ssh ubuntu@${aws_instance.intern_server.public_ip}"
}
