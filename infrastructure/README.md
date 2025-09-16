# AWS Batch Infrastructure for VeriCoding

This Terraform configuration sets up AWS Batch for running verification tasks with automatic scaling to 0 cost when idle.

## Key Features

- **Auto-scales to 0**: `minvCpus = 0`, `desiredvCpus = 0`
- **Spot instances**: c8g.2xlarge (ARM Graviton3) at 100% on-demand bid
- **Cost-optimized**: Only pay when jobs are running
- **Lean 4 optimized**: Job definition configured for Lean verification tasks

## Architecture

- **Compute Environment**: Managed EC2 spot instances
- **Instance Type**: c8g.2xlarge (8 vCPUs, 16GB RAM)
- **Networking**: VPC with public subnets across 2 AZs
- **Auto-scaling**: 0-80 vCPUs (max 10 machines) based on job queue demand

## Usage

### 1. Configure Variables (Optional)

```bash
cd infrastructure
cp terraform.tfvars.example terraform.tfvars
# Edit terraform.tfvars to customize settings
```

### 2. Deploy Infrastructure

```bash
# Using the Docker wrapper script
./tf init
./tf plan
./tf apply

# Or with direct docker command:
# docker run -it -v $(pwd):/workspace -v ~/.aws:/root/.aws:ro -w /workspace hashicorp/terraform:latest init
```

### 2. Submit Jobs

```bash
# Example: Submit a Lean verification job
aws batch submit-job \
  --job-name "lean-verification-$(date +%s)" \
  --job-queue vericoding-job-queue \
  --job-definition lean-verification \
  --parameters '{"sourceCode":"theorem example : 1 + 1 = 2 := by simp"}'
```

### 3. Monitor Jobs

```bash
# List jobs
aws batch list-jobs --job-queue vericoding-job-queue

# Get job details
aws batch describe-jobs --jobs JOB_ID
```

## Cost Estimation

- **c8g.2xlarge spot**: ~$0.05-0.15/hour (vs $0.34 on-demand)
- **Idle cost**: $0 (scales to 0)
- **Typical job**: 1-15 minutes = $0.001-0.04 per job

## Job Definition

**lean-verification**: Lean 4 theorem proving and verification tasks

## Cleanup

```bash
terraform destroy
```