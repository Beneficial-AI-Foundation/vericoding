# Tests

This directory contains the test suite for the vericoding package.

## Test Organization

- `test_imports.py` - Tests for package imports and module availability
- `test_llm_providers.py` - Tests for LLM provider functionality and inheritance
- `test_config.py` - Tests for configuration validation and language configurations
- `test_prompts.py` - Tests for prompt loading functionality
- `test_cli.py` - Tests for CLI interfaces and command-line functionality

## Running Tests

### Using pytest directly:
```bash
# Run all tests
uv run pytest

# Run with verbose output
uv run pytest -v

# Run specific test file
uv run pytest tests/test_imports.py

# Run with coverage
uv run pytest --cov=vericoding --cov-report=html

# Run with coverage and detailed missing lines
uv run pytest --cov=vericoding --cov-report=term-missing
```

### Using the test runner script:
```bash
# Run all tests
python run_tests.py

# Run tests with coverage (terminal output)
python run_tests.py --coverage

# Run tests with HTML coverage report
python run_tests.py --coverage-html

# Run with additional pytest arguments
python run_tests.py --cov-report=xml
```

### Using uv with test dependencies:
```bash
# Install test dependencies and run tests
uv sync --extra test
uv run pytest
```

## Test Dependencies

Test dependencies are defined in `pyproject.toml` under `[project.optional-dependencies.test]`:
- pytest
- pytest-cov (for coverage reporting)

## Configuration

- `pytest.ini` - Main pytest configuration
- `.coveragerc` - Coverage reporting configuration

## Coverage Reporting

The project includes comprehensive coverage reporting:

### Current Coverage
- **Minimum required**: 25%
- **Current coverage**: ~29%
- **Goal**: Gradually increase coverage as more tests are added

### Coverage Reports
- **Terminal**: Shows coverage percentages and missing lines
- **HTML**: Interactive coverage report in `htmlcov/index.html`
- **XML**: Machine-readable coverage data in `coverage.xml`

### Coverage Exclusions
The following are excluded from coverage calculations:
- Test files themselves
- Debug/development code
- Abstract methods
- Type checking imports
- `__repr__` methods
- Non-runnable code (if `__name__ == "__main__"`)

### CI/CD Coverage
- Automatic coverage reporting in GitHub Actions
- Coverage comments on pull requests
- Codecov integration for coverage tracking
- Coverage artifacts uploaded for each CI run

## CI/CD

Tests are automatically run in GitHub Actions via `.github/workflows/python-tests.yml` on:
- Push to main or develop branches
- Pull requests to main or develop branches
- When test-related files are modified

## Migration from Workflow Tests

These tests were extracted from the original GitHub workflow inline tests to provide:
- Better organization and maintainability
- Easier local development and debugging
- Standard pytest features (fixtures, parametrization, etc.)
- Coverage reporting
- IDE integration
