# Trace Analysis Guide

This guide explains how to work with conversation traces from VeriCoding experiments.

## Overview

Conversation traces capture the complete interaction between the system and Claude, including:
- All prompts and responses
- MCP tool invocations
- Verification attempts and results
- Final generated code

## Storage

### WANDB Artifacts (Recommended)

When `WANDB_API_KEY` is set, traces are automatically uploaded to WANDB artifacts:

```bash
# Set your WANDB API key
export WANDB_API_KEY=your_key_here

# Run experiments - traces will be uploaded automatically
uv run python -m vericoding.lean.spec_to_code_lean_sdk ./lean_specs/
```

Benefits:
- No local storage bloat
- Version controlled traces
- Easy sharing with team
- Won't affect git operations

### Local Storage (Fallback)

If WANDB is not configured, traces are saved to `experiment_traces/` directory.

**WARNING**: These files can be large and should NEVER be committed to git!

## Downloading Traces from WANDB

### Using WANDB CLI

```bash
# Install WANDB CLI
pip install wandb

# Login
wandb login

# Download a specific artifact
wandb artifact get vericoding-traces/trace_example_spec_abc123:v0

# Download all traces from a run
wandb artifact get-all vericoding-traces --type experiment_trace
```

### Using Python

```python
import wandb

# Initialize WANDB
run = wandb.init(project="vericoding-traces")

# Download a specific trace artifact
artifact = run.use_artifact('trace_example_spec_abc123:latest')
artifact_dir = artifact.download()

# Load and analyze the trace
from vericoding.tools.trace_logger import TraceLogger
trace_logger = TraceLogger()

# Find the trace file
import glob
trace_files = glob.glob(f"{artifact_dir}/*.json.gz")
for trace_file in trace_files:
    trace = trace_logger.load_trace(trace_file)
    # Analyze trace...
```

## Analysis Tools

### Basic Analysis

```bash
# Analyze traces from a directory
uv run vericode-analyze-traces path/to/downloaded/traces/

# Generate full report
uv run vericode-analyze-traces path/to/traces/ --patterns --strategies --report analysis.json
```

### Custom Analysis

```python
from vericoding.tools.trace_logger import TraceLogger
from vericoding.tools.analyze_traces import analyze_trace_directory

# Load traces
trace_logger = TraceLogger()
trace = trace_logger.load_trace("path/to/trace.json.gz")

# Access conversation turns
for turn in trace.turns:
    print(f"Turn {turn.turn_number}")
    print(f"Prompt: {turn.prompt[:100]}...")
    print(f"Tools used: {[t['name'] for t in turn.tools_used]}")
    print(f"Response length: {len(turn.response)}")
    print("-" * 80)

# Check verification results
for i, result in enumerate(trace.verification_results):
    print(f"Verification {i+1}: {'Success' if result['success'] else 'Failed'}")
```

## Finding Patterns

The analysis tools can identify:

1. **Quick Success**: Problems solved on first attempt
2. **Heavy Tool Usage**: Experiments using many MCP tools
3. **Repeated Errors**: Similar failures across attempts
4. **Successful Strategies**: Common patterns in successful experiments

## Best Practices

1. **Always use WANDB** for production experiments to avoid git issues
2. **Tag experiments** appropriately for easy filtering
3. **Analyze patterns** across multiple experiments
4. **Extract strategies** from successful traces
5. **Document findings** in experiment reports

## Troubleshooting

### WANDB Upload Failed

If traces fail to upload:
- Check `WANDB_API_KEY` is set correctly
- Verify internet connection
- Check WANDB project permissions
- Traces will be saved locally as fallback

### Large Trace Files

For very long conversations:
- Traces are automatically compressed (gzip)
- WANDB handles large artifacts well
- Consider setting iteration limits for experiments

### Analysis Performance

For analyzing many traces:
- Use batch processing
- Filter by metadata before loading full traces
- Use the summary files for quick overview