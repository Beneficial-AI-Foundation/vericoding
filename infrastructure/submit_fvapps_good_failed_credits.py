#!/usr/bin/env python3

import subprocess
import json
from datetime import datetime

# CHANGE THESE
SHORTNAME = "fvapps-good-retry"
LONGNAME = "benchmarks/lean/fvapps_good/files"

# Generate a timestamp tag for this batch of experiments
timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
tag = f"{SHORTNAME}-{timestamp}"

# Configuration
NUM_SHARDS = 9

print(f"Submitting retry experiments with tag: {tag}")
print(f"Only submitting jobs that failed due to insufficient credits")

# Define failed model/shard combinations from credit report
failed_jobs = [
    # gemini - all 9 shards failed
    ("gemini", [1, 2, 3, 4, 5, 6, 7, 8, 9]),
    # glm - shards 3, 6, 7 failed
    ("glm", [3, 6, 7]),
    # gpt - all 9 shards failed
    ("gpt", [1, 2, 3, 4, 5, 6, 7, 8, 9]),
    # gpt-mini - all 9 shards failed
    ("gpt-mini", [1, 2, 3, 4, 5, 6, 7, 8, 9])
]

# Region configurations
regions = [
    {"region": "eu-west-2", "job_queue": "vericoding-job-queue", "job_definition": "lean-verification"},
    {"region": "eu-west-1", "job_queue": "vericoding2-job-queue", "job_definition": "lean-verification2"},
    {"region": "us-east-1", "job_queue": "vericoding3-job-queue", "job_definition": "lean-verification3"},
    {"region": "us-east-2", "job_queue": "vericoding4-job-queue", "job_definition": "lean-verification4"},
]

def submit_job(model, region_config, shard):
    """Submit a single job"""
    # Create job name with sanitized model name
    sanitized_model = ''.join(c if c.isalnum() else '-' for c in model)
    job_name = f"{tag}-exp-{sanitized_model}-shard{shard}-{int(datetime.now().timestamp())}"
    
    print(f"Submitting job: {job_name} with model: {model} shard {shard} to region: {region_config['region']}")
    
    # Build the command
    command = [
        "aws", "batch", "submit-job",
        "--region", region_config["region"],
        "--job-name", job_name,
        "--job-queue", region_config["job_queue"],
        "--job-definition", region_config["job_definition"],
        "--container-overrides", json.dumps({
            "command": [
                "/bin/bash",
                "-c",
                f"apt-get update && apt-get install -y curl && curl -fsSL https://raw.githubusercontent.com/Beneficial-AI-Foundation/vericoding/batch_experiments/infrastructure/run.sh | bash -s batch_experiments {LONGNAME} --llm {model} --tag {tag} --shard {shard}/{NUM_SHARDS}"
            ]
        })
    ]
    
    # Submit the job and extract job ID
    result = subprocess.run(command, capture_output=True, text=True, check=True)
    job_response = json.loads(result.stdout)
    return job_response["jobId"]

# Submit jobs for each failed model/shard combination, cycling through regions
job_index = 0
total_jobs = 0

for model, failed_shards in failed_jobs:
    for shard in failed_shards:
        region_config = regions[job_index % len(regions)]
        job_id = submit_job(model, region_config, shard)
        print(job_id)
        job_index += 1
        total_jobs += 1

print(f"All {total_jobs} retry experiments submitted with tag: {tag}")
print("Failed job breakdown:")
for model, failed_shards in failed_jobs:
    print(f"  {model}: {len(failed_shards)} shards ({failed_shards})")
print("To monitor jobs:")
print("for status in SUBMITTED PENDING RUNNABLE STARTING RUNNING; do")
print("    aws batch list-jobs --job-queue vericoding-job-queue --job-status $status")
print("done")