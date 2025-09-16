#!/bin/bash

# Script to store API keys in AWS Systems Manager Parameter Store
set -euo pipefail

AWS_REGION="${AWS_REGION:-us-west-2}"

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
store_parameter "openai-api-key" "OpenAI API Key"
store_parameter "wandb-api-key" "Weights & Biases API Key"
store_parameter "anthropic-api-key" "Anthropic API Key"

echo
echo "API keys stored successfully!"
echo "Your Batch jobs will now have access to these keys as environment variables:"
echo "  - OPENAI_API_KEY"
echo "  - WANDB_API_KEY" 
echo "  - ANTHROPIC_API_KEY"
echo
echo "To view stored parameters:"
echo "  aws ssm get-parameters-by-path --path /vericoding --recursive --with-decryption"