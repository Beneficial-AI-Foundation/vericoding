#!/usr/bin/env bash

# Copy .env file to all durian servers
# Usage: ./copy_env.sh

set -e

if [ ! -f .env ]; then
    echo "Error: .env file not found in current directory"
    exit 1
fi

echo "=== Copying .env to all durian servers ==="
echo ""

# durian1
echo "Copying to durian1..."
scp -o StrictHostKeyChecking=no .env durian1:~/vericoding/
echo "✓ durian1 done"

# durian2
echo "Copying to durian2..."
scp -o StrictHostKeyChecking=no .env durian2:~/vericoding/
echo "✓ durian2 done"

# durian3
echo "Copying to durian3..."
scp -o StrictHostKeyChecking=no .env durian3:~/vericoding/
echo "✓ durian3 done"

# durian4
echo "Copying to durian4..."
scp -o StrictHostKeyChecking=no .env durian4:~/vericoding/
echo "✓ durian4 done"

# durian5
echo "Copying to durian5..."
scp -o StrictHostKeyChecking=no .env durian5:~/vericoding/
echo "✓ durian5 done"

# durian6
echo "Copying to durian6..."
scp -o StrictHostKeyChecking=no .env durian6:~/vericoding/
echo "✓ durian6 done"

# durian7
echo "Copying to durian7..."
scp -o StrictHostKeyChecking=no .env durian7:~/vericoding/
echo "✓ durian7 done"

# durian8
echo "Copying to durian8..."
scp -o StrictHostKeyChecking=no .env durian8:~/vericoding/
echo "✓ durian8 done"

# durian9
echo "Copying to durian9..."
scp -o StrictHostKeyChecking=no .env durian9:~/vericoding/
echo "✓ durian9 done"

# durian10
echo "Copying to durian10..."
scp -o StrictHostKeyChecking=no .env durian10:~/vericoding/
echo "✓ durian10 done"

echo ""
echo "=== All .env files copied successfully ==="