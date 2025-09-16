#!/usr/bin/env bash

set -e

# Generate a timestamp tag for this batch of experiments
TIMESTAMP=$(date +%Y%m%d-%H%M%S)
TAG="batch-${TIMESTAMP}"

echo "Submitting experiments with tag: ${TAG}"

# Define models to test (from batch_experiments.py)
MODELS=(
    "claude-opus"
    "claude-sonnet"
    "deepseek"
    "gemini-pro"
    "gemini-flash"
    "glm"
    "gpt"
    "gpt-mini"
    "grok"
    "grok-code"
)

# Function to submit a single job
submit_job() {
    local model="$1"
    local job_name="exp-${model//[^a-zA-Z0-9]/-}-$(date +%s)"
    
    echo "Submitting job: ${job_name} with model: ${model}"
    
    aws batch submit-job \
        --job-name "${job_name}" \
        --job-queue vericoding-job-queue \
        --job-definition lean-verification \
        --container-overrides "{
            \"command\": [
                \"/bin/bash\",
                \"-c\",
                \"apt-get update && apt-get install -y curl && curl -fsSL https://raw.githubusercontent.com/Beneficial-AI-Foundation/vericoding/batch_experiments/infrastructure/run.sh | bash -s batch_experiments --model ${model} --dataset verified_cogen --limit 1 --tag ${TAG}\"
            ]
        }"
}

# Submit jobs for each model
for model in "${MODELS[@]}"; do
    submit_job "${model}"
    echo "Job submitted for model: ${model}"
    echo "---"
done

echo "All experiments submitted with tag: ${TAG}"
echo "To monitor jobs: aws batch list-jobs --job-queue vericoding-job-queue --job-status SUBMITTED,PENDING,RUNNABLE,STARTING,RUNNING"