terraform {
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }
  }
}

provider "aws" {
  region = "eu-west-2"  # London - same region as haggis
}

# Data source to get the latest Ubuntu 24.04 LTS AMI
data "aws_ami" "ubuntu" {
  most_recent = true
  owners      = ["099720109477"] # Canonical

  filter {
    name   = "name"
    values = ["ubuntu/images/hvm-ssd-gp3/ubuntu-noble-24.04-*"]
  }

  filter {
    name   = "architecture"
    values = ["arm64"]  # For c8g instances
  }

  filter {
    name   = "virtualization-type"
    values = ["hvm"]
  }
}

# Create 10 NEW EC2 instances (separate from existing haggis)
resource "aws_instance" "vericoding_servers" {
  count                  = 10
  ami                    = data.aws_ami.ubuntu.id
  instance_type          = "c8g.2xlarge"
  key_name              = "aws-ec2-20250224"
  vpc_security_group_ids = ["sg-0f7a3df675cb3fd68"]
  subnet_id             = "subnet-0b7f1623a2aa277b2"
  
  user_data = base64encode(file("${path.module}/initial_setup.sh"))

  # Add more storage if needed
  root_block_device {
    volume_type = "gp3"
    volume_size = 30
    encrypted   = true
  }

  tags = {
    Name = "durian${count.index + 1}"
    Purpose = "vericoding-experiments"
    Server-ID = count.index + 1
  }
}

# Note: Using dynamic public IPs instead of Elastic IPs to avoid AWS limits
# Each instance will get a public IP automatically

# Output the IP addresses and instance IDs
output "instance_details" {
  value = {
    for i in range(10) : i + 1 => {
      instance_id = aws_instance.vericoding_servers[i].id
      public_ip   = aws_instance.vericoding_servers[i].public_ip
      name        = aws_instance.vericoding_servers[i].tags.Name
    }
  }
}

output "ssh_config" {
  value = join("\n\n", [
    for i in range(10) : 
    "Host ${aws_instance.vericoding_servers[i].tags.Name}\n    User ubuntu\n    HostName ${aws_instance.vericoding_servers[i].public_ip}\n    IdentityFile ~/Downloads/aws-ec2-20250224.pem"
  ])
  description = "SSH config entries for durian1-durian10"
}