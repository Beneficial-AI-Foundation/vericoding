# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- **Large Context Window Support**: Added support for Claude 3.5 Sonnet with 1M input tokens
  - New `context_window_config.py` module for managing model context capabilities
  - `EnhancedLLMProvider` class with automatic model selection based on input size
  - Context window analysis and optimization utilities
  - Backward compatibility with existing models
  - Comprehensive test suite for new functionality
  - Documentation and examples for large context use cases

### Changed

- Updated default Claude model to `claude-3-5-sonnet-20241022` (1M input tokens)
- Enhanced LLM provider factory to support automatic model selection
- Improved error handling and fallback mechanisms

### Features

- **Automatic Model Selection**: System automatically chooses optimal model based on input size
- **Context Window Analysis**: Analyze text and get model recommendations
- **Large Codebase Processing**: Process entire projects in single API calls
- **Token Estimation**: Approximate token counting for context optimization
- **Usage Statistics**: Track model usage for optimization
- **Fallback Support**: Automatic fallback to alternative providers/models

### Documentation

- Added comprehensive documentation in `docs/large_context_window.md`
- Created demonstration script in `examples/large_context_demo.py`
- Updated API documentation and usage examples

### Testing

- Added comprehensive test suite in `tests/test_context_window_config.py`
- Created GitHub workflow for testing large context functionality
- Added backward compatibility tests
- Added integration tests with existing codebase

## [Previous versions]

[Add previous version history here when available]
