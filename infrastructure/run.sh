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

# Notify that script has started
echo "Script started on $(hostname) for branch $BRANCH"

# Update system and install git
echo "Updating package lists..."
apt-get update

echo "Installing git and curl..."
apt-get install -y git curl

# Clone vericoding repository
echo "Cloning vericoding repository..."
git clone https://github.com/Beneficial-AI-Foundation/vericoding.git

cd vericoding

# Switch to the specified branch
echo "Checking out branch: $BRANCH"
git checkout "$BRANCH"

# Install uv (Python package manager)
echo "Installing uv..."
curl -LsSf https://astral.sh/uv/install.sh | sh
export PATH="$HOME/.cargo/bin:$PATH"

source $HOME/.local/bin/env

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
if lake exe cache get; then
    echo "Cache downloaded successfully!"
else
    echo "Cache download failed, falling back to clean build..."
    lake clean
    lake build benchmarks/lean/clever/files/clever_0.lean
fi

# Notify completion
echo "Setup complete on $(hostname) for branch $BRANCH"

echo "Vericoding environment ready!"

uv run src/vericoder.py lean "${@:2}"

echo "Done with experiment"
