#!/bin/bash

# Lean 4 setup script for AWS Batch jobs
set -euo pipefail

echo "Setting up Lean 4 environment..."

# Update package lists
apt-get update -qq

# Install essential dependencies
apt-get install -y \
    curl \
    git \
    build-essential \
    cmake \
    libgmp-dev \
    zlib1g-dev \
    ca-certificates \
    --no-install-recommends

# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable

# Add elan to PATH
export PATH="$HOME/.elan/bin:$PATH"

# Verify installation
echo "Lean version:"
lean --version

echo "Lake version:"  
lake --version

echo "Lean 4 setup complete!"