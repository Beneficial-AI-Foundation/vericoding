# VeriCoding Lean Module

Modern Lean 4 verification experiment framework with Claude Code SDK integration.

## Features

- **Pydantic-based prompts**: Type-safe, composable prompt management
- **Claude Code SDK integration**: Native support for MCP tools
- **WANDB experiment tracking**: Comprehensive experiment logging and comparison
- **Modular architecture**: Clean separation of concerns

## Architecture

### Core Components

1. **`prompts.py`**: Pydantic models for type-safe prompts
   - `LeanPromptConfig`: Configuration for prompts
   - `GenerateCodePrompt`: Initial code generation
   - `FixVerificationPrompt`: Error fixing
   - `LeanPromptManager`: Central prompt management

2. **`lean_agent.py`**: Modern agent using Claude Code SDK
   - `LeanAgent`: Main agent class with MCP support
   - `VerificationResult`: Structured verification results
   - `AgentState`: State management across iterations

3. **`tracker.py`**: WANDB experiment tracking
   - `LeanExperimentTracker`: Track and log experiments
   - `run_experiment()`: Run full experiments
   - `run_comparison_experiment()`: Compare baseline vs MCP

4. **`prompt_loader.py`**: Backward compatibility layer
   - Supports existing YAML-based prompts
   - Provides migration path to Pydantic

## Usage

### Basic Usage

```python
from vericoding.lean import run_lean_agent
from pathlib import Path

# Process a single file
result = run_lean_agent(
    Path("example.lean"),
    use_mcp=True,
    max_iterations=5
)
```

### Running Experiments

```python
from vericoding.lean import run_experiment

# Run experiment with MCP tools
summary = run_experiment(
    spec_dir=Path("./lean_specs"),
    name="my_experiment",
    use_mcp=True,
    max_files=10
)
```

### Comparison Experiments

```python
from vericoding.lean import run_comparison_experiment

# Compare baseline vs MCP performance
comparison = run_comparison_experiment(
    spec_dir=Path("./lean_specs"),
    max_files=5
)
```

### Custom Agent Usage

```python
from vericoding.lean import LeanAgent

# Create custom agent
agent = LeanAgent(use_mcp=True)

# Process specification
state = agent.process_spec_file(Path("spec.lean"))
print(f"Success: {state.success}")
print(f"Iterations: {len(state.iterations)}")
```

## MCP Tools

When `use_mcp=True`, the agent has access to:

- `lean_goal`: Check proof state at specific locations
- `lean_diagnostic_messages`: Get all diagnostics
- `lean_hover_info`: Get documentation for symbols
- `lean_leansearch`: Natural language theorem search
- `lean_loogle`: Type-based theorem search
- `lean_state_search`: Goal-based theorem search
- And more...

## Environment Variables

- `ANTHROPIC_API_KEY`: Required for Claude API access
- `WANDB_API_KEY`: Optional, enables WANDB tracking
- `LEAN_PATH`: Path to Lean executable (default: "lean")

## Migration from Legacy Code

The module maintains backward compatibility with the original YAML-based system:

```python
# Legacy usage still works
from vericoding.lean import PromptLoader
loader = PromptLoader()  # Uses YAML if available
prompt = loader.format_prompt("generate_code", code="...")
```

## Example Files

See `example_usage.py` for comprehensive examples of all features.