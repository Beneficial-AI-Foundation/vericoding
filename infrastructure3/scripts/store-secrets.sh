#!/usr/bin/env bash

# Script to store API keys in AWS Systems Manager Parameter Store
set -euo pipefail

AWS_REGION="${AWS_REGION:-us-east-1}"

echo "Storing API keys in AWS Systems Manager Parameter Store..."
echo "Region: $AWS_REGION"

# Function to store a parameter
store_parameter() {
    local name="$1"
    local description="$2"
    
    echo -n "Enter $description: "
    read -s value
    echo
    
    if [ -n "$value" ]; then
        aws ssm put-parameter \
            --region "$AWS_REGION" \
            --name "/vericoding/$name" \
            --value "$value" \
            --type "SecureString" \
            --description "$description for VeriCoding project" \
            --overwrite
        echo "✓ Stored $description"
    else
        echo "⚠ Skipped $description (empty value)"
    fi
}

# Store API keys
store_parameter "wandb-api-key" "Weights & Biases API Key"
store_parameter "openrouter-api-key" "OpenRouter API Key"
store_parameter "fake-api-key" "Fake API Key for testing"

echo
echo "API keys stored successfully!"
echo "Your Batch jobs will now have access to these keys as environment variables:"
echo "  - WANDB_API_KEY"
echo "  - OPENROUTER_API_KEY" 
echo "  - FAKE_API_KEY"
echo
echo "To view stored parameters:"
echo "  aws ssm get-parameters-by-path --path /vericoding --recursive --with-decryption"
