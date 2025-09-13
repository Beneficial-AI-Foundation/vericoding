#!/bin/bash

# Terraform deployment script for vericoding servers

set -e

echo "=== Vericoding Server Deployment ==="

# Initialize Terraform if not done already
if [ ! -d ".terraform" ]; then
    echo "Initializing Terraform..."
    terraform init
fi

# Plan the deployment
echo "Planning deployment..."
terraform plan -out=tfplan

# Ask for confirmation
read -p "Deploy 10 vericoding servers? (y/N): " confirm
if [[ $confirm != [yY] ]]; then
    echo "Deployment cancelled"
    exit 1
fi

# Apply the plan
echo "Deploying infrastructure..."
terraform apply tfplan

# Save the SSH config
echo "Generating SSH config..."
terraform output -raw ssh_config > ../ssh_config_servers

echo ""
echo "=== Deployment Complete ==="
echo "SSH config saved to: ssh_config_servers"
echo ""
echo "To add to your ~/.ssh/config, run:"
echo "cat ssh_config_servers >> ~/.ssh/config"
echo ""
echo "Instance details:"
terraform output -json instance_details | jq -r 'to_entries[] | "Durian\(.key): \(.value.name) - \(.value.public_ip) (\(.value.instance_id))"'

echo ""
echo "=== Next Steps ==="
echo "1. Wait a few minutes for setup scripts to complete"
echo "2. Copy .env files to each server:"
echo "   for i in {1..10}; do"
echo "     scp your-env-file ubuntu@\$(terraform output -json instance_details | jq -r '.\"\$i\".public_ip'):/home/ubuntu/vericoding/.env"
echo "   done"
echo ""
echo "3. Test connection to all servers:"
echo "   for i in {1..10}; do ssh durian\$i 'echo Durian \$i ready'; done"