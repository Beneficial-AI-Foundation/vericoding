#!/bin/bash

# Manual setup script for vericoding servers
# Run this after SSH'ing into each durian server

set -e

echo "=== Vericoding Server Setup ==="
echo "Starting setup at $(date)"

# Update system
echo "Updating system packages..."
sudo apt-get update && sudo apt-get upgrade -y

# Install essential packages
echo "Installing essential packages..."
sudo apt-get install -y curl git build-essential

# Install uv (Python package manager)
echo "Installing uv..."
curl -LsSf https://astral.sh/uv/install.sh | sh

# Install elan (Lean version manager) 
echo "Installing elan..."
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y

# Add paths to bashrc
echo "Setting up PATH..."
echo 'export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"' >> ~/.bashrc

# Source the new PATH
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"

# Get lake cache (assumes repo is already cloned)
echo "Getting lake cache (this may take a few minutes)..."
cd ~/vericoding
lake exe cache get

# Create directory for .env files
mkdir -p ~/vericoding/.env_temp

# Signal completion
touch ~/setup_complete

echo ""
echo "=== Setup Complete! ==="
echo "✅ uv installed: $(which uv)"
echo "✅ elan installed: $(which elan)"
echo "✅ lake installed: $(which lake)"
echo "✅ vericoding repo ready"
echo "✅ lake cache downloaded"
echo ""
echo "Next steps:"
echo "1. Copy your .env file to ~/vericoding/.env"
echo "2. Run experiments!"