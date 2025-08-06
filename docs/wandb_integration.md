# Weights & Biases Integration

Track verification experiments with W&B metrics.

## Setup

```bash
export WANDB_API_KEY=your_key
export WANDB_PROJECT=vericoding  # optional
export WANDB_ENTITY=your_team    # optional
```

## Usage

Metrics are automatically logged during verification runs. Disable with:

```bash
export WANDB_MODE=disabled
```

## Tracked Metrics

- **Verification attempts**: Success rate, iteration count, error patterns
- **LLM usage**: API calls, latency, token usage, cumulative costs
- **Performance**: Files/minute, average iterations per file

## Example

```python
from vericoding.utils.wandb_logger import get_wandb_logger

logger = get_wandb_logger()
logger.init_run(config={"language": "lean", "model": "claude"})

# Metrics logged automatically during processing
logger.log_verification("file.lean", iteration=1, success=False, error_text="Type error")
logger.log_llm_call(model="claude", latency_ms=2500, cost_usd=0.02)

logger.summary({"total_files": 10, "success_files": 8})
logger.finish()
```

See `examples/wandb_integration.py` for complete example.
