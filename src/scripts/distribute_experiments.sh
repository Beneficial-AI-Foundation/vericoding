#!/usr/bin/env bash

# Distribute experiments across 10 durian servers with cost limit
# Usage: ./distribute_experiments.sh <cost_limit>
# Example: ./distribute_experiments.sh 100

set -e

if [ $# -ne 1 ]; then
    echo "Usage: $0 <cost_limit>"
    echo "Example: $0 100"
    exit 1
fi

COST_LIMIT=$1

# Get current commit hash
CURRENT_COMMIT=$(git rev-parse HEAD)

echo "=== Distributing Experiments Across Durian Servers ==="
echo "Cost limit: \$${COST_LIMIT}"
echo "Current commit: ${CURRENT_COMMIT}"
echo ""

# Calculate total experiments (7 datasets × 10 models = 70 experiments)
TOTAL_EXPERIMENTS=70
EXPERIMENTS_PER_SERVER=7

echo "Total experiments: ${TOTAL_EXPERIMENTS}"
echo "Experiments per server: ${EXPERIMENTS_PER_SERVER}"
echo ""

# durian1: experiments 0-6
echo "=== Starting durian1 (experiments: 0,1,2,3,4,5,6) ==="
ssh -o StrictHostKeyChecking=no durian1 "tmux kill-session -t experiments 2>/dev/null || true; tmux kill-session -t experiments 2>/dev/null || true; tmux new-session -d -s experiments 'bash -l -c \"cd ~/vericoding && git pull && git checkout ${CURRENT_COMMIT} && uv run src/scripts/batch_experiments.py --cost-limit ${COST_LIMIT} --run \\\"0,1,2,3,4,5,6\\\"; exec bash\"'" &
echo "✓ durian1 started in tmux session 'experiments'"

# durian2: experiments 7-13
echo "=== Starting durian2 (experiments: 7,8,9,10,11,12,13) ==="
ssh -o StrictHostKeyChecking=no durian2 "tmux kill-session -t experiments 2>/dev/null || true; tmux new-session -d -s experiments 'bash -l -c \"cd ~/vericoding && git pull && git checkout ${CURRENT_COMMIT} && uv run src/scripts/batch_experiments.py --cost-limit ${COST_LIMIT} --run \\\"7,8,9,10,11,12,13\\\"; exec bash\"'" &
echo "✓ durian2 started in tmux session 'experiments'"

# durian3: experiments 14-20
echo "=== Starting durian3 (experiments: 14,15,16,17,18,19,20) ==="
ssh -o StrictHostKeyChecking=no durian3 "tmux kill-session -t experiments 2>/dev/null || true; tmux new-session -d -s experiments 'bash -l -c \"cd ~/vericoding && git pull && git checkout ${CURRENT_COMMIT} && uv run src/scripts/batch_experiments.py --cost-limit ${COST_LIMIT} --run \\\"14,15,16,17,18,19,20\\\"; exec bash\"'" &
echo "✓ durian3 started in tmux session 'experiments'"

# durian4: experiments 21-27
echo "=== Starting durian4 (experiments: 21,22,23,24,25,26,27) ==="
ssh -o StrictHostKeyChecking=no durian4 "tmux kill-session -t experiments 2>/dev/null || true; tmux new-session -d -s experiments 'bash -l -c \"cd ~/vericoding && git pull && git checkout ${CURRENT_COMMIT} && uv run src/scripts/batch_experiments.py --cost-limit ${COST_LIMIT} --run \\\"21,22,23,24,25,26,27\\\"; exec bash\"'" &
echo "✓ durian4 started in tmux session 'experiments'"

# durian5: experiments 28-34
echo "=== Starting durian5 (experiments: 28,29,30,31,32,33,34) ==="
ssh -o StrictHostKeyChecking=no durian5 "tmux kill-session -t experiments 2>/dev/null || true; tmux new-session -d -s experiments 'bash -l -c \"cd ~/vericoding && git pull && git checkout ${CURRENT_COMMIT} && uv run src/scripts/batch_experiments.py --cost-limit ${COST_LIMIT} --run \\\"28,29,30,31,32,33,34\\\"; exec bash\"'" &
echo "✓ durian5 started in tmux session 'experiments'"

# durian6: experiments 35-41
echo "=== Starting durian6 (experiments: 35,36,37,38,39,40,41) ==="
ssh -o StrictHostKeyChecking=no durian6 "tmux kill-session -t experiments 2>/dev/null || true; tmux new-session -d -s experiments 'bash -l -c \"cd ~/vericoding && git pull && git checkout ${CURRENT_COMMIT} && uv run src/scripts/batch_experiments.py --cost-limit ${COST_LIMIT} --run \\\"35,36,37,38,39,40,41\\\"; exec bash\"'" &
echo "✓ durian6 started in tmux session 'experiments'"

# durian7: experiments 42-48
echo "=== Starting durian7 (experiments: 42,43,44,45,46,47,48) ==="
ssh -o StrictHostKeyChecking=no durian7 "tmux kill-session -t experiments 2>/dev/null || true; tmux new-session -d -s experiments 'bash -l -c \"cd ~/vericoding && git pull && git checkout ${CURRENT_COMMIT} && uv run src/scripts/batch_experiments.py --cost-limit ${COST_LIMIT} --run \\\"42,43,44,45,46,47,48\\\"; exec bash\"'" &
echo "✓ durian7 started in tmux session 'experiments'"

# durian8: experiments 49-55
echo "=== Starting durian8 (experiments: 49,50,51,52,53,54,55) ==="
ssh -o StrictHostKeyChecking=no durian8 "tmux kill-session -t experiments 2>/dev/null || true; tmux new-session -d -s experiments 'bash -l -c \"cd ~/vericoding && git pull && git checkout ${CURRENT_COMMIT} && uv run src/scripts/batch_experiments.py --cost-limit ${COST_LIMIT} --run \\\"49,50,51,52,53,54,55\\\"; exec bash\"'" &
echo "✓ durian8 started in tmux session 'experiments'"

# durian9: experiments 56-62
echo "=== Starting durian9 (experiments: 56,57,58,59,60,61,62) ==="
ssh -o StrictHostKeyChecking=no durian9 "tmux kill-session -t experiments 2>/dev/null || true; tmux new-session -d -s experiments 'bash -l -c \"cd ~/vericoding && git pull && git checkout ${CURRENT_COMMIT} && uv run src/scripts/batch_experiments.py --cost-limit ${COST_LIMIT} --run \\\"56,57,58,59,60,61,62\\\"; exec bash\"'" &
echo "✓ durian9 started in tmux session 'experiments'"

# durian10: experiments 63-69 (last 7 experiments)
echo "=== Starting durian10 (experiments: 63,64,65,66,67,68,69) ==="
ssh -o StrictHostKeyChecking=no durian10 "tmux kill-session -t experiments 2>/dev/null || true; tmux new-session -d -s experiments 'bash -l -c \"cd ~/vericoding && git pull && git checkout ${CURRENT_COMMIT} && uv run src/scripts/batch_experiments.py --cost-limit ${COST_LIMIT} --run \\\"63,64,65,66,67,68,69\\\"; exec bash\"'" &
echo "✓ durian10 started in tmux session 'experiments'"

echo ""
echo "=== All Experiments Started ==="
echo ""
echo "To monitor progress on each server:"
echo "  ssh durian1 'tmux attach -t experiments'"
echo "  ssh durian2 'tmux attach -t experiments'"
echo "  ssh durian3 'tmux attach -t experiments'"
echo "  ssh durian4 'tmux attach -t experiments'"
echo "  ssh durian5 'tmux attach -t experiments'"
echo "  ssh durian6 'tmux attach -t experiments'"
echo "  ssh durian7 'tmux attach -t experiments'"
echo "  ssh durian8 'tmux attach -t experiments'"
echo "  ssh durian9 'tmux attach -t experiments'"
echo "  ssh durian10 'tmux attach -t experiments'"

echo ""
echo "To check which experiments are running:"
echo "  ssh durian1 'ps aux | grep vericoder'"
echo ""
echo "To stop all experiments:"
echo "  ssh durian1 'tmux kill-session -t experiments'"
echo "  ssh durian2 'tmux kill-session -t experiments'"
echo "  ssh durian3 'tmux kill-session -t experiments'"
echo "  ssh durian4 'tmux kill-session -t experiments'"
echo "  ssh durian5 'tmux kill-session -t experiments'"
echo "  ssh durian6 'tmux kill-session -t experiments'"
echo "  ssh durian7 'tmux kill-session -t experiments'"
echo "  ssh durian8 'tmux kill-session -t experiments'"
echo "  ssh durian9 'tmux kill-session -t experiments'"
echo "  ssh durian10 'tmux kill-session -t experiments'"
