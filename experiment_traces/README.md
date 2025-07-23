# Experiment Traces

This directory contains detailed conversation traces from spec-to-code generation experiments.

## Overview

Each trace captures:
- Full conversation history between the user prompts and Claude's responses
- All MCP tool invocations and their results
- Verification attempts and outcomes
- Final generated code
- Metadata about the experiment

## File Format

Traces are saved as compressed JSON files (`.json.gz`) to save space while preserving all details.

### Naming Convention
```
trace_{language}_{filename}_{timestamp}_{experiment_id}.json.gz
```

Example: `trace_lean_example_spec_20240115_143022_abc123.json.gz`

## Trace Structure

Each trace contains:
- `experiment_id`: Unique identifier for the experiment
- `file_name`: Original specification file processed
- `language`: Programming language (lean, dafny, verus)
- `use_mcp`: Whether MCP tools were enabled
- `turns`: Array of conversation turns with prompts and responses
- `verification_results`: Array of verification attempts
- `final_code`: The final generated code

## Analysis Tools

Use the provided analysis script to examine traces:

```bash
# Basic analysis
uv run vericode-analyze-traces experiment_traces/

# Find patterns
uv run vericode-analyze-traces experiment_traces/ --patterns

# Extract successful strategies
uv run vericode-analyze-traces experiment_traces/ --strategies

# Save full report
uv run vericode-analyze-traces experiment_traces/ --report analysis_report.json
```

## Markdown Reports

Each experiment also generates a human-readable markdown report saved in the output directory:
```
{output_dir}/{filename}_trace_report.md
```

These reports include:
- Formatted conversation flow
- Tool usage details
- Verification results
- Final generated code

## Privacy Note

Traces may contain:
- Full code snippets
- Error messages
- API responses

This directory is gitignored by default to prevent accidental commits of large trace files.