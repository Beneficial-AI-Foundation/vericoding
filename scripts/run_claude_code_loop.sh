#!/usr/bin/env bash
set -euo pipefail

# Continuous runner for Lean sample with Claude Code + MCP.
# Requires: ANTHROPIC_API_KEY in env; Node + @anthropic-ai/claude-code installed; lake/lean.

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"
SRC_DIR="$ROOT_DIR/src"
SAMPLE_DIR="$ROOT_DIR/benchmarks/lean/dafnybench/Sample"

echo "Running continuous Claude Code loop on: $SAMPLE_DIR"
echo "Press Ctrl-C to stop."

while true; do
  uv run -q python "$SRC_DIR/spec_to_code.py" \
    lean "$SAMPLE_DIR" \
    --iterations 1 \
    --workers 1 \
    --llm-provider claude \
    --llm-model claude-opus-4-1 \
    --use-mcp \
    --tool-calling \
    --no-wandb \
    --lake-build-target Benchmarks || true
  echo "Sleeping 60s..."
  sleep 60
done

