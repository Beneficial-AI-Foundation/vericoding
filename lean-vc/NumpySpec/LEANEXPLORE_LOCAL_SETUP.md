# LeanExplore Local MCP Setup

This project is configured to use LeanExplore with a local backend, requiring NO API keys.

## Setup Complete ✅

1. **LeanExplore installed**: `lean-explore==0.3.0`
2. **Local data downloaded**: Located at `~/.lean_explore/data/toolchains/0.2.0/`
3. **MCP configuration updated**: `.mcp.json` configured for local backend

## Configuration

The `.mcp.json` file is configured to run LeanExplore with local data:

```json
{
  "mcpServers": {
    "lean-lsp-mcp": {
      "command": "uvx",
      "args": ["lean-lsp-mcp"]
    },
    "leanexplore": {
      "command": "uv",
      "args": [
        "run",
        "python",
        "-m",
        "lean_explore.mcp.server",
        "--backend",
        "local"
      ]
    }
  }
}
```

## Usage

### Via MCP (for AI assistants like Claude)

The MCP server runs automatically when accessed by AI assistants. It provides tools for:
- Searching Lean declarations
- Looking up definitions
- Finding related theorems

### Direct CLI Usage

```bash
# Download/update local data
uv run leanexplore data fetch

# Run MCP server manually (for testing)
uv run leanexplore mcp serve --backend local

# Search locally without MCP
uv run leanexplore search "List.sort" --limit 10
```

## Local Data

The local backend uses:
- SQLite database: `lean_explore_data.db`
- FAISS vector index: `main_faiss.index`
- ID mapping: `faiss_ids_map.json`

These files contain indexed Lean 4 declarations from:
- Mathlib4
- Lean standard library
- Other major Lean projects

## No API Key Required ✅

This setup runs entirely locally:
- No internet connection needed after initial data download
- No API keys required
- All searches performed against local database
- Privacy-preserving (no data sent to external services)

## Justfile Commands

```bash
# Install MCP tools (includes LeanExplore)
just install-mcp-tools

# Verify MCP setup
just verify-mcp

# Full setup including MCP
just setup
```

## Example Output

Running `uv run python demo_leanexplore_local.py` shows:

```
═══ LeanExplore Local Search Demo ═══

Running entirely locally - NO API KEY REQUIRED!

✅ Local service initialized
📁 Using data from: ~/.lean_explore/data/toolchains/

🔍 Searching for: qsort

Found 5 results:

╭────────────────────────────────── Result 1 ──────────────────────────────────╮
│ Name: Array.qsort                                                            │
│ Type: Unknown                                                                │
│ File: Init/Data/Array/QSort.lean                                             │
│                                                                              │
│ Sorts an array using the Quicksort algorithm.                               │
│                                                                              │
│ The optional parameter `lt` specifies an ordering predicate...              │
╰──────────────────────────────────────────────────────────────────────────────╯

[Additional results shown...]

✨ Demo complete - all searches performed locally!
```

## Key Points

- ✅ **Completely Local**: No internet connection needed after data download
- ✅ **No API Key**: Works without any authentication
- ✅ **Fast**: Searches against local FAISS index
- ✅ **Privacy**: No data sent to external servers