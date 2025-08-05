# Weights & Biases Integration for VeriCoding

This document describes how to use Weights & Biases (wandb) for experiment tracking, logging, and ablation studies in the VeriCoding project.

## Overview

The VeriCoding project now includes comprehensive wandb integration for tracking:
- Experiment configurations and hyperparameters
- File processing status and progress
- LLM API call metrics (latency, tokens, costs)
- Verification attempts and success rates
- Code artifacts (especially Lean source code)
- Experiment summaries and performance metrics

## Quick Start

### 1. Set up wandb account (if needed)

```bash
# Install wandb (already included in project dependencies)
uv sync

# Login to wandb
wandb login
```

### 2. Run experiments with wandb tracking

```bash
# Run with wandb tracking enabled (default)
python spec_to_code.py lean ./lean/benchmarks --iterations 5

# Disable wandb tracking
python spec_to_code.py lean ./lean/benchmarks --iterations 5 --no-wandb
```

### 3. Configure wandb via environment variables

```bash
# Set in .env file or export
export WANDB_PROJECT="vericoding-experiments"
export WANDB_ENTITY="your-team-or-username"
export WANDB_MODE="online"  # or "offline" for local logging
```

## Features

### 1. Automatic Experiment Tracking

Every run automatically logs:
- **Configuration**: Language, LLM provider/model, max iterations, worker count
- **File Processing**: Status updates for each file (started, success, failed)
- **Verification Attempts**: Each iteration with success/failure and error details
- **LLM Metrics**: API calls, latency, token usage (if available)
- **Summary Statistics**: Success rates, total iterations, processing time

### 2. Code Artifact Management

Lean code is automatically saved as wandb artifacts:
- Original specification files
- Generated implementations
- Fixed versions after each iteration
- Properly typed as "lean_code" for better organization

### 3. Real-time Monitoring

View experiment progress in real-time at [wandb.ai](https://wandb.ai):
- Live metrics and charts
- File processing status
- Error logs and debugging information
- Comparative analysis across runs

## Usage Examples

### Basic Experiment

```python
# The main script handles everything automatically
python spec_to_code.py lean ./specs --iterations 3
```

### Ablation Studies

Run experiments with different configurations:

```bash
# Experiment 1: Baseline
python spec_to_code.py lean ./benchmarks --iterations 5 --llm-model claude-3-5-sonnet

# Experiment 2: More iterations
python spec_to_code.py lean ./benchmarks --iterations 10 --llm-model claude-3-5-sonnet

# Experiment 3: Different model
python spec_to_code.py lean ./benchmarks --iterations 5 --llm-model gpt-4

# Compare results in wandb dashboard
```

### Custom Logging

For custom scripts, use the wandb logger directly:

```python
from vericoding.utils.wandb_logger import get_wandb_logger, init_wandb_run

# Initialize run
init_wandb_run(
    name="custom_lean_experiment",
    config={"custom_param": "value"},
    tags=["lean", "custom"]
)

# Get logger instance
logger = get_wandb_logger()

# Log custom metrics
logger.log_file_processing(
    file_path="example.lean",
    language="lean",
    status="processing",
    metrics={"custom_metric": 42}
)

# Log Lean code artifact
logger.log_code_artifact(
    file_path="example.lean",
    code=lean_code_content,
    version="v1",
    metadata={"theorem_count": 5}
)
```

## Logged Metrics

### File-level Metrics
- `file`: File being processed
- `language`: Programming language
- `status`: started/success/failed/error
- `iteration`: Current iteration number
- `error`: Error message (if failed)

### Verification Metrics
- `verification/{filename}/iteration`: Iteration number
- `verification/{filename}/success`: Boolean success status
- `verification/{filename}/error_count`: Number of errors
- `verification/{filename}/fix_type`: Type of fix applied

### LLM Metrics
- `llm/{prompt_type}/calls`: Number of API calls
- `llm/{prompt_type}/model`: Model used
- `llm/{prompt_type}/latency_ms`: Response time
- `llm/{prompt_type}/input_tokens`: Input token count
- `llm/{prompt_type}/output_tokens`: Output token count
- `llm/{prompt_type}/cost_usd`: Estimated cost

### Summary Metrics
- `summary/total_files`: Total files processed
- `summary/successful_files`: Successfully verified files
- `summary/failed_files`: Failed verification files
- `summary/success_rate`: Overall success rate
- `summary/total_iterations`: Total iterations across all files
- `summary/avg_iterations_per_file`: Average iterations needed
- `summary/duration_seconds`: Total processing time

## Best Practices

1. **Use meaningful run names**: Include experiment parameters in the run name
2. **Tag experiments**: Use tags like "lean", "ablation", "baseline" for organization
3. **Log configurations**: Ensure all relevant parameters are logged
4. **Save artifacts**: Code artifacts help with debugging and analysis
5. **Monitor in real-time**: Check wandb dashboard during long runs

## Troubleshooting

### Disable wandb if needed
```bash
python spec_to_code.py lean ./specs --no-wandb
```

### Offline mode for air-gapped environments
```bash
export WANDB_MODE=offline
python spec_to_code.py lean ./specs
# Later sync with: wandb sync
```

### Debug logging issues
```python
# Check if logger is initialized
logger = get_wandb_logger()
print(f"Logger initialized: {logger._initialized}")
print(f"Run URL: {logger.run.url if logger.run else 'No run'}")
```

## Advanced Features

### Custom Artifacts

Save additional artifacts:
```python
logger.log_text_artifact(
    name="verification_report",
    text=detailed_report,
    metadata={"report_type": "verification"}
)
```

### Hyperparameter Sweeps

Use wandb sweeps for systematic exploration:
```yaml
# sweep.yaml
program: spec_to_code.py
method: grid
parameters:
  iterations:
    values: [3, 5, 10]
  llm-model:
    values: ["claude-3-5-sonnet", "gpt-4"]
command:
  - python
  - spec_to_code.py
  - lean
  - ./benchmarks
  - --iterations
  - ${iterations}
  - --llm-model
  - ${llm-model}
```

Run with: `wandb sweep sweep.yaml`