# Weights & Biases Integration

Advanced verification experiment tracking with failure analysis.

## Setup

```bash
export WANDB_API_KEY=your_key
export WANDB_PROJECT=vericoding  # optional
export WANDB_ENTITY=your_team    # optional
```

## Features

### Direct wandb API Usage
No wrapper needed - use wandb directly:

```python
import wandb

# Initialize run
run = wandb.init(project="vericoding", config={"language": "lean"})

# Log metrics
wandb.log({"verify/file1/success": 1, "llm/latency_ms": 1500})

# Finish run
wandb.finish()
```

### Failure Collection & Analysis

Track verification failures for pattern analysis:

```python
from vericoding.analysis import FailureCollector

collector = FailureCollector()
collector.add_failure(
    file_path="theorem.lean",
    iteration=1,
    spec_code=spec,
    generated_code=code,
    error_msg=error
)
collector.log_to_wandb()  # Creates table and artifacts
```

### LLM Judge for Post-Hoc Analysis

Analyze failures with LLM to identify root causes:

```python
from vericoding.analysis import FailureAnalyzer

analyzer = FailureAnalyzer()
# Analyze specific run
report = analyzer.analyze_run(run_id)

# Analyze patterns across runs
patterns = analyzer.analyze_cross_run_patterns(last_n_runs=10)

# Generate improvement recommendations
recommendations = analyzer.generate_improvement_report(report)
```

## Key Metrics Tracked

- **Verification attempts**: Success/failure by file and iteration
- **Error categorization**: Type mismatches, missing lemmas, incomplete proofs
- **LLM usage**: API calls, latency, cumulative costs
- **Failure artifacts**: All failed code versions stored for analysis
- **Cross-run patterns**: Files that consistently fail across experiments

## Advanced Features

### Failure Tables
Structured tracking of all failures with:
- File, iteration, spec/code hashes
- Error messages and proof states  
- Automatic categorization
- Queryable via wandb API

### Code Artifacts
Each failed verification creates versioned artifacts:
- Complete code lineage from spec to final attempt
- Enables reproduction of any failure
- Builds dataset for future training

### Automated Analysis
Post-run analysis identifies:
- Root causes via LLM analysis
- Fix suggestions with confidence scores
- Problematic specification patterns
- Success strategies from similar past fixes

## Examples

See complete examples:
- `examples/wandb_analysis_demo.py` - Full workflow demo
- `examples/wandb_integration.py` - Basic metrics tracking

## Environment Variables

- `WANDB_API_KEY`: Required for wandb tracking
- `WANDB_PROJECT`: Project name (default: "vericoding")
- `WANDB_ENTITY`: Team/organization name
- `WANDB_MODE`: "online", "offline", or "disabled"

Disable tracking with `--no-wandb` flag or by not setting `WANDB_API_KEY`.