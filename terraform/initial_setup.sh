#!/bin/bash

# Initial setup script - just clone the repo
# Run this immediately after SSH'ing into a fresh durian server

set -e

echo "=== Initial Vericoding Setup ==="
echo "Cloning vericoding repository..."

# Install git if not present
sudo apt-get update
sudo apt-get install -y git

# Clone the vericoding repository (theo-experiments branch)
cd ~
git clone -b theo-experiments https://github.com/Beneficial-AI-Foundation/vericoding

echo ""
echo "✅ Repository cloned to ~/vericoding (theo-experiments branch)"
echo ""
echo "Next step: cd ~/vericoding && bash terraform/setup.sh"