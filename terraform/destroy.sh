#!/usr/bin/env bash

# Terraform destroy script for vericoding servers (using Docker)

set -e

echo "=== Vericoding Server Destruction ==="

# Docker wrapper function for Terraform
terraform_docker() {
    docker run -i -t \
        -v "$(pwd):/workspace" \
        -v "$HOME/.aws:/root/.aws:ro" \
        -v "$HOME/Downloads:/root/Downloads:ro" \
        -w /workspace \
        hashicorp/terraform:latest \
        "$@"
}

# Show what will be destroyed
echo "Planning destruction..."
terraform_docker plan -destroy

echo ""
echo "⚠️  WARNING: This will destroy all durian1-durian10 servers!"
echo "   (haggis will remain untouched)"
echo ""

# Ask for confirmation
read -p "Destroy all 10 durian servers? Type 'yes' to confirm: " confirm
if [[ $confirm != "yes" ]]; then
    echo "Destruction cancelled"
    exit 1
fi

# Destroy the infrastructure
echo "Destroying infrastructure..."
terraform_docker destroy -auto-approve

echo ""
echo "=== Destruction Complete ==="
echo "All durian servers have been destroyed."
echo "Your haggis server remains unchanged."
echo ""
echo "Cleanup:"
echo "- Remove durian entries from ~/.ssh/config if needed"
echo "- Local Terraform state has been updated"
