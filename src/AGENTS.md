# AGENTS.md — src subtree

Scope: This file applies to the entire `src/` directory and all its subfolders.

Summary (2025-09-08)
- Merged the best of `~/vericoding/src/spec_to_code.py` into this tree:
  - Added CLI flags: `--use-mcp`, `--tool-calling`, `--reasoning-effort`, `--lake-build-target`.
  - Lean output now goes under `benchmarks/lean/dafnybench_gen/Run_<ts>/...` to avoid polluting default targets.
  - Added Lean MCP helper: `vericoding/lean/mcp_helpers.py`.
  - Integrated Claude Code SDK as the default Anthropic provider (`ClaudeCodeProvider`) using `lean-lsp-mcp` via MCP.
  - Fixed `determine_input_type` bug (removed dangling `spec_files` variable).
  - Made `vericoding/lean/__init__.py` lazy to avoid heavy imports blocking MCP usage.
  - Changed Lean verification to run with repo context: `lake env lean {file}` (runner uses repo root as `cwd`).

What works
- `spec_to_code.py --llm-provider claude` invokes the Claude Code SDK provider.
- Claude Code options are built with:
  - `model=claude-opus-4-1`
  - `allowed_tools=[Read, Write, Grep, Search, Bash, mcp__lean-lsp-mcp]`
  - MCP server via stdio: `lake env uvx lean-lsp-mcp`
  - `CLAUDE.md` is injected as a system prompt layer.
- Verification calls for Lean run out of the repo root (`cwd`), which is necessary for Lake + Mathlib.

Current caveats
- MCP startup: printing shows `MCP (lean-lsp-mcp): Not available (import/start failed)` at runtime.
  - Root cause: the persistent stdio session via `mcp.client.stdio.stdio_client` sometimes triggers an anyio cancel-scope teardown error on startup/exit. We masked one common case, but current `mcp==1.13.x` emits a different error (“Attempted to exit cancel scope in a different task”).
  - The submodule import trap in `vericoding/lean/__init__.py` (pydantic validation on import) has been fixed with lazy imports; the remaining issue is the stdio client lifecycle.
- Without a valid `ANTHROPIC_API_KEY`, the Claude Code SDK returns an exit status 1 error (expected). For local smoke tests we set a dummy key to pass provider creation, but queries still fail.
- The sample file `benchmarks/lean/dafnybench/Sample/SampleTheorem.lean` imports `Mathlib`; if mathlib cache is invalid or Lake state is cold, single-file compile may warn. Running `lake build` at repo root will warm caches.

How to run locally
- Prereqs: `uv` (Python 3.12), `lake`, `elan`, and optionally `Mathlib` via Lake manifest.
- Install deps: `uv sync` (run at repo root).
- Set key: `export ANTHROPIC_API_KEY=...`.
- MCP availability quick check (binary): `uvx lean-lsp-mcp --help` should exit 0.
- Run one-shot sample (no W&B):
  - `uv run python src/spec_to_code.py lean benchmarks/lean/dafnybench/Sample -i 1 -w 1 --use-mcp --tool-calling --no-wandb`
  - You should see `LLM Provider: claude` and `LLM Model: claude-opus-4-1`.
  - MCP currently prints “Not available”; see TODO below.

Coding conventions for this subtree
- Avoid heavy imports in package `__init__.py`; prefer lazy imports or local imports inside functions.
- When calling external tools for Lean, use `lake env` and set `cwd` to the repo root to inherit Lake context.
- Keep CLI options consistent across languages; only Lean should enable MCP.

Next TODOs
- MCP robustness
  - [ ] Replace/augment persistent stdio session with a reliable HTTP (`streamable-http`) fallback and expose a `--mcp-transport=http|stdio` flag.
  - [ ] Expand the monkey patch to silence known anyio teardown errors (“Attempted to exit cancel scope ...”) and log detailed diagnostics to `logs/lean_mcp.log`.
  - [ ] In `spec_to_code.py`, if stdio session fails, attempt one-shot HTTP tool listing and print tools to confirm MCP toolchain availability.
- Claude Code provider
  - [ ] Map `--reasoning-effort` to Claude Code options (`max_thinking_tokens`) with sensible defaults.
  - [ ] Parse and persist Claude Code file write/edit events to mirror agent-side changes into our output/debug directories.
  - [ ] Add a `--claude-text-only` switch to revert to standard Anthropic (non-agent) if desired.
- Lean verification
  - [ ] Switch sample to avoid `import Mathlib` or add a tiny module under Benchmarks that compiles in a fresh checkout.
  - [ ] Optionally support module-based verification (e.g., `lake build Benchmarks:<module>`) when available.
- Observability
  - [ ] Always create `logs/lean_mcp.log` and `logs/lean_mcp.stderr.log` with verbose output when `--debug` is set.
  - [ ] Add a `--dry-run` to lint/mcp-check without calling the LLM.

Decision record
- Kept Claude Code SDK as the default for provider `claude`. This unlocks MCP tool usage and repository-aware actions.
- Did not keep CI automation (workflow + loop script) after review; users can run locally or add their own CI.

