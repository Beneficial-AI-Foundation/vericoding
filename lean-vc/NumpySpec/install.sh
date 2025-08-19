#!/usr/bin/env bash
# Thin installation script for codex - installs just and runs setup
set -euo pipefail

echo "🚀 NumpySpec Installation"
echo "========================"

# Install just if not present
if ! command -v just >/dev/null 2>&1; then
    echo "📦 Installing just..."
    if [[ "$OSTYPE" == "darwin"* ]] && command -v brew >/dev/null 2>&1; then
        brew install just
    else
        curl --proto '=https' --tlsv1.2 -sSf https://just.systems/install.sh | bash -s -- --to ~/.local/bin
        export PATH="$HOME/.local/bin:$PATH"
    fi
fi

# Run the main setup
echo "🔧 Running setup..."
just setup

echo ""
echo "✅ Installation complete!"
echo "💡 If PATH was updated, restart your shell or run: source ~/.zshrc (or ~/.bashrc)"