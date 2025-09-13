#!/bin/bash

# Exit on any error
set -e

# Update system
export DEBIAN_FRONTEND=noninteractive
apt-get update && apt-get upgrade -y

# Install essential packages
apt-get install -y curl git build-essential

# Install uv (Python package manager)
curl -LsSf https://astral.sh/uv/install.sh | sh

# Add uv to PATH for the current session and future sessions
export PATH="$HOME/.local/bin:$PATH"
echo 'export PATH="$HOME/.local/bin:$PATH"' >> /home/ubuntu/.bashrc

# Install elan (Lean version manager)
sudo -u ubuntu bash -c 'curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y'

# Add elan to PATH
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> /home/ubuntu/.bashrc
export PATH="/home/ubuntu/.elan/bin:$PATH"

# Clone the vericoding repository as ubuntu user
sudo -u ubuntu bash -c 'cd /home/ubuntu && git clone https://github.com/Beneficial-AI-Foundation/vericoding'

# Change to the vericoding directory and get lake cache
sudo -u ubuntu bash -c 'cd /home/ubuntu/vericoding && source ~/.bashrc && lake exe cache get'

# Create a directory for .env files
sudo -u ubuntu mkdir -p /home/ubuntu/vericoding/.env_temp

# Set proper permissions
chown -R ubuntu:ubuntu /home/ubuntu/vericoding

# Log completion
echo "Setup completed at $(date)" >> /var/log/vericoding-setup.log

# Signal that setup is complete
sudo -u ubuntu touch /home/ubuntu/setup_complete