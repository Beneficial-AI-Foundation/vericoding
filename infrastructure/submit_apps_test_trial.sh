#!/usr/bin/env bash

set -e

# CHANGE THESE
shortname="apps_test"
longname="benchmarks/lean/apps_from_dafny_apps/files"

# Generate a timestamp tag for this batch of experiments
TIMESTAMP=$(date +%Y%m%d-%H%M%S)

TAG="$shortname-${TIMESTAMP}"

echo "Submitting experiments with tag: ${TAG}"

# Define models to test (from batch_experiments.py)
MODELS=(
    "claude-opus"
    "claude-sonnet"
    "deepseek"
    "gemini"
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
    local job_name="$TAG-exp-${model//[^a-zA-Z0-9]/-}-$(date +%s)"
    
    echo "Submitting job: ${job_name} with model: ${model}"
    
    aws batch submit-job \
        --region eu-west-1 \
        --job-name "${job_name}" \
        --job-queue vericoding2-job-queue \
        --job-definition lean-verification2 \
        --container-overrides "{
            \"command\": [
                \"/bin/bash\",
                \"-c\",
                \"apt-get update && apt-get install -y curl && curl -fsSL https://raw.githubusercontent.com/Beneficial-AI-Foundation/vericoding/batch_experiments/infrastructure/run.sh | bash -s batch_experiments $longname --llm ${model} --tag ${TAG} --limit 10\"
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
echo "To monitor jobs:"
echo "for status in SUBMITTED PENDING RUNNABLE STARTING RUNNING; do"
echo    'aws batch list-jobs --job-queue vericoding-job-queue --job-status $status'
echo done
