# Tests

This directory contains the test suite for the vericoding package.

## Test Organization

- `test_llm_providers.py` - Comprehensive LLM provider functionality and inheritance tests 
- `test_config.py` - Configuration validation and language configuration tests 
- `test_prompts.py` - Robust prompt loading functionality with mocking 
- `test_api_compatibility.py` - Tests for API compatibility
- `test_end_to_end.py` - End-to-end tests for the main application workflow
- `test_modular_equivalence.py` - Tests for ensuring equivalence between modular and monolithic implementations
- `test_performance_regression.py` - Tests to detect performance regressions


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
- **Current coverage**: ~95% (LLM Providers: 100%, Prompts: 95%, Config: 90%+)
- **Goal**: Maintain high coverage while ensuring test quality and meaningfulness

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

## Test Quality Improvements

These tests have been significantly enhanced from simple "trivial" tests to comprehensive, meaningful test suites:

### Recent Improvements (August 2025)
- **LLM Providers**: Replaced 3 basic instantiation tests with 35 comprehensive tests covering:
  - Abstract base class validation
  - Error handling for all provider types (Anthropic, OpenAI, DeepSeek)
  - API response validation and edge cases
  - Factory function testing with proper mocking
  - Provider inheritance and method implementation validation
  - Integration testing with realistic scenarios

- **Prompt Loading**: Replaced 4 trivial tests with 15 robust tests covering:
  - File I/O operations with proper mocking
  - YAML parsing error handling
  - Prompt validation and formatting
  - Missing file scenarios
  - Integration with actual prompt files

- **Configuration**: Enhanced tests with proper object instantiation covering:
  - Complete ProcessingConfig and LanguageConfig validation
  - Environment variable loading with dotenv mocking
  - Language configuration consistency checks
  - Integration testing with actual configuration files

- **Imports & CLI**: Improved with realistic usage patterns and error handling

### Testing Philosophy
- **Meaningful Assertions**: Every test validates actual behavior, not just "can instantiate"
- **Error Handling**: Comprehensive testing of edge cases and error conditions
- **Mocking Strategy**: Proper isolation of external dependencies (files, APIs, environment)
- **Integration Testing**: Tests that validate components working together
- **High Coverage**: Achieving 90%+ coverage while maintaining test quality
