#!/usr/bin/env bash
set -euo pipefail

# Run a full Lean generation with MCP in a tmux session so it survives terminal crashes.
# Usage: ./scripts/run_overnight.sh

SESSION="vericoding_overnight"
CMD="uv run src/spec_to_code.py lean ./benchmarks/lean/dafnybench --iterations 2 --workers 4 --use-mcp --llm-provider openai --llm-model gpt-5 --reasoning-effort high --api-rate-limit-delay 1 --debug"

if ! command -v tmux >/dev/null 2>&1; then
  echo "tmux not found. Please install tmux to use this script." >&2
  exit 1
fi

if tmux has-session -t "$SESSION" 2>/dev/null; then
  echo "Session $SESSION already exists. Attach with: tmux attach -t $SESSION"
  exit 0
fi

tmux new-session -d -s "$SESSION" "$CMD; echo; echo '=== DONE ==='; sleep 3600"
echo "Started tmux session: $SESSION"
echo "Attach with: tmux attach -t $SESSION"

