# Tests

Comprehensive test suite for code2verus to catch breaking changes in CI.

## Running Tests

```bash
./scripts/test.sh          # Full suite (lint + type check + all tests)
./scripts/test.sh --smoke  # Quick smoke tests only
./scripts/test.sh --config # Config tests only
```

## Test Categories

### `test_config.py` - Configuration Management
- Config file loading and validation
- Default values and overrides
- System prompts and YAML instructions
- Forbidden field enforcement
- Custom config file handling

### `test_smoke.py` - CI Smoke Tests
Quick validation that core functionality works:

**TestSmokeTests**
- Import validation (all modules load)
- Config loads without errors
- Entry points exist and are callable
- Agent creation works
- Basic translation flow (mocked)
- Critical config values present
- Language handling (supported/unsupported)

**TestCriticalPathsWork**
- Default prompts accessible
- Model configuration valid
- Async processing setup
- Error handling infrastructure
- Verification tools available

**TestDataIntegrity**
- YAML structure consistency
- Prompt consistency across languages
- Field mapping rules documented
- CLI tool invocation

### `test_*.py` - Component Tests
Individual test files for:
- `test_translation.py`: AI translation logic
- `test_verification.py`: Verus compilation and checking
- `test_benchmarks.py`: Dataset loading (HF + local)
- `test_integration.py`: End-to-end workflows

## Test Strategy

- **Smoke tests**: Fast validation for CI (< 1 min)
- **Component tests**: Isolated unit testing with mocking
- **Integration tests**: Real workflows with test data
- **Config tests**: Validation of all configuration scenarios

Tests use mocking to avoid API calls and external dependencies in CI.
