#!/usr/bin/env python3

import subprocess
import json
from datetime import datetime

# CHANGE THESE
SHORTNAME = "verified-cogen"
LONGNAME = "benchmarks/lean/verified_cogen/files"

# Generate a timestamp tag for this batch of experiments
timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
tag = f"{SHORTNAME}-{timestamp}"

print(f"Submitting experiments with tag: {tag}")

# Define models to test (from batch_experiments.py)
models=[
    "claude-opus",
    "claude-sonnet",
    "deepseek",
    "gemini",
    "gemini-flash",
    "glm",
    "gpt",
    "gpt-mini",
    "grok",
    "grok-code",
]

def submit_job(model):
    """Submit a single job"""
    # Create job name with sanitized model name
    sanitized_model = ''.join(c if c.isalnum() else '-' for c in model)
    job_name = f"{tag}-exp-{sanitized_model}-{int(datetime.now().timestamp())}"
    
    print(f"Submitting job: {job_name} with model: {model}")
    
    # Build the command
    command = [
        "aws", "batch", "submit-job",
        "--region", "eu-west-2",
        "--job-name", job_name,
        "--job-queue", "vericoding-job-queue",
        "--job-definition", "lean-verification",
        "--container-overrides", json.dumps({
            "command": [
                "/bin/bash",
                "-c",
                f"apt-get update && apt-get install -y curl && curl -fsSL https://raw.githubusercontent.com/Beneficial-AI-Foundation/vericoding/batch_experiments/infrastructure/run.sh | bash -s batch_experiments {LONGNAME} --llm {model} --tag {tag} "
            ]
        })
    ]
    
    # Submit the job and extract job ID
    result = subprocess.run(command, capture_output=True, text=True, check=True)
    job_response = json.loads(result.stdout)
    return job_response["jobId"]

# Submit jobs for each model
for model in models:
    job_id = submit_job(model)
    print(job_id)

print(f"All experiments submitted with tag: {tag}")
print("To monitor jobs:")
print("for status in SUBMITTED PENDING RUNNABLE STARTING RUNNING; do")
print("    aws batch list-jobs --job-queue vericoding-job-queue --job-status $status")
print("done")
