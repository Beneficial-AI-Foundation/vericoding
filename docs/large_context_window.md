# Large Context Window Support

This document describes the enhanced support for large context windows in VeriCoding, particularly the new Claude 3.5 Sonnet with 1M input tokens.

## Overview

The VeriCoding project now supports models with large context windows, enabling more sophisticated code generation and verification tasks. The flagship addition is **Claude 3.5 Sonnet** with **1M input tokens**, which provides 4x the input context of previous models.

## Key Features

### 1. Automatic Model Selection

The system automatically selects the optimal model based on input size:

```python
from vericoding.core import get_optimal_model_for_text, estimate_token_count

# Small text - uses efficient model
small_text = "Write a simple function"
optimal_model = get_optimal_model_for_text(small_text)
# Returns: claude-3-5-haiku-20241022 (200K context)

# Large text - uses large context model
large_text = "Analyze this entire codebase..."  # 500K+ tokens
optimal_model = get_optimal_model_for_text(large_text)
# Returns: claude-3-5-sonnet-20241022 (1M context)
```

### 2. Context Window Analysis

Analyze text and get recommendations:

```python
from vericoding.core import get_context_analysis

analysis = get_context_analysis(large_text)
print(f"Estimated tokens: {analysis['estimated_tokens']:,}")
print(f"Recommended model: {analysis['recommended_model']}")
print(f"Suitable models: {len(analysis['suitable_models'])}")
```

### 3. Enhanced LLM Provider

Use the enhanced provider for automatic optimization:

```python
from vericoding.core import EnhancedLLMProvider

provider = EnhancedLLMProvider(
    preferred_provider="claude",
    auto_model_selection=True
)

# Automatically selects best model
response = provider.call_api_with_context_optimization(prompt)
```

## Supported Models

### Claude Models

| Model                        | Input Tokens | Output Tokens | Total Tokens | Use Case                              |
| ---------------------------- | ------------ | ------------- | ------------ | ------------------------------------- |
| `claude-3-5-sonnet-20241022` | 1,000,000    | 200,000       | 1,200,000    | Large codebases, complex verification |
| `claude-3-5-haiku-20241022`  | 200,000      | 200,000       | 400,000      | General purpose, efficient            |
| `claude-3-opus-20240229`     | 200,000      | 200,000       | 400,000      | High-quality generation               |
| `claude-3-sonnet-20240229`   | 200,000      | 200,000       | 400,000      | Balanced performance                  |
| `claude-3-haiku-20240307`    | 200,000      | 200,000       | 400,000      | Fast processing                       |

### OpenAI Models

| Model         | Input Tokens | Output Tokens | Total Tokens | Use Case        |
| ------------- | ------------ | ------------- | ------------ | --------------- |
| `gpt-4o`      | 128,000      | 128,000       | 256,000      | General purpose |
| `gpt-4o-mini` | 128,000      | 128,000       | 256,000      | Cost-effective  |

### DeepSeek Models

| Model           | Input Tokens | Output Tokens | Total Tokens | Use Case             |
| --------------- | ------------ | ------------- | ------------ | -------------------- |
| `deepseek-chat` | 128,000      | 128,000       | 256,000      | Alternative provider |

## Use Cases for 1M Token Context

### 1. Large Codebase Analysis

Process entire projects in a single API call:

```python
from vericoding.core import EnhancedLLMProvider

provider = EnhancedLLMProvider()

# Analyze entire project
prompt = f"""
Analyze this codebase and provide:
1. Architecture overview
2. Code quality assessment
3. Security vulnerabilities
4. Performance optimizations
5. Refactoring suggestions

Codebase:
{codebase_content}
"""

response = provider.call_api_with_context_optimization(prompt)
```

### 2. Complex Verification Tasks

Handle large verification specifications with all dependencies:

```python
# Large Lean 4 verification task
large_spec = """
# Include entire mathematical library
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

# Large theorem with many lemmas
theorem complex_mathematical_property (n : Nat) :
  -- 1000+ lines of complex mathematical reasoning
  -- All lemmas and definitions included in context
"""

response = provider.call_api_with_context_optimization(large_spec)
```

### 3. Multi-File Code Generation

Generate code that spans multiple files with full context:

```python
prompt = f"""
Generate a complete web application with:
- Frontend (React/TypeScript)
- Backend (Python/FastAPI)
- Database schema
- API documentation
- Tests

Requirements:
{requirements}

Existing codebase context:
{existing_files}
"""

response = provider.call_api_with_context_optimization(prompt)
```

### 4. Documentation Generation

Generate comprehensive documentation from large codebases:

```python
prompt = f"""
Generate comprehensive documentation for this codebase:
- API reference
- Architecture diagrams
- Usage examples
- Troubleshooting guide
- Performance considerations

Codebase:
{codebase_content}
"""

response = provider.call_api_with_context_optimization(prompt)
```

## Configuration

### Environment Variables

```bash
# Required for Claude models
export ANTHROPIC_API_KEY="your-api-key"

# Optional for fallback providers
export OPENAI_API_KEY="your-openai-key"
export DEEPSEEK_API_KEY="your-deepseek-key"
```

### Python Configuration

```python
from vericoding.core import EnhancedLLMProvider

# Basic configuration
provider = EnhancedLLMProvider(
    preferred_provider="claude",
    auto_model_selection=True
)

# Advanced configuration
provider = EnhancedLLMProvider(
    preferred_provider="claude",
    fallback_providers=["openai", "deepseek"],
    auto_model_selection=True,
    max_input_tokens=800_000  # Leave buffer
)
```

## Performance Considerations

### Token Estimation

The system uses approximate token estimation:

```python
from vericoding.core import estimate_token_count

# Rough estimation (1 token ≈ 4 characters)
tokens = estimate_token_count("Hello world")  # ≈ 3 tokens
```

### Context Utilization

Monitor context usage for optimization:

```python
analysis = provider.get_context_analysis(text)
for model_info in analysis['suitable_models']:
    print(f"{model_info['model']}: {model_info['utilization_percent']:.1f}%")
```

### Cost Optimization

- Use smaller models for simple tasks
- Reserve large context models for complex tasks
- Monitor usage statistics

```python
stats = provider.get_usage_stats()
for model, count in stats.items():
    print(f"{model}: {count} calls")
```

## Migration Guide

### From Previous Models

1. **Update model names**:

   ```python
   # Old
   model = "claude-sonnet-4-20250514"

   # New (recommended)
   model = "claude-3-5-sonnet-20241022"
   ```

2. **Enable auto-selection**:

   ```python
   # Old: Manual model selection
   provider = create_llm_provider("claude", "claude-sonnet-4-20250514")

   # New: Automatic selection
   provider = EnhancedLLMProvider(auto_model_selection=True)
   ```

3. **Leverage large context**:

   ```python
   # Old: Split large inputs
   chunks = split_large_input(text)
   for chunk in chunks:
       response = provider.call_api(chunk)

   # New: Single API call
   response = provider.call_api_with_context_optimization(text)
   ```

## Best Practices

### 1. Model Selection

- Let the system auto-select for optimal performance
- Use specific models only when needed
- Monitor usage patterns

### 2. Context Management

- Include relevant context but avoid unnecessary content
- Use structured prompts for large inputs
- Consider chunking for extremely large content

### 3. Error Handling

```python
try:
    response = provider.call_api_with_context_optimization(prompt)
except Exception as e:
    # Fallback to smaller context or chunking
    print(f"Large context failed: {e}")
    # Implement fallback strategy
```

### 4. Monitoring

```python
# Track usage
stats = provider.get_usage_stats()
print(f"Model usage: {stats}")

# Analyze context utilization
analysis = provider.get_context_analysis(prompt)
print(f"Context efficiency: {analysis['context_utilization']}")
```

## Examples

See `examples/large_context_demo.py` for comprehensive examples demonstrating:

- Context window analysis
- Optimal model selection
- Large codebase processing
- Verification use cases
- Performance monitoring

## Troubleshooting

### Common Issues

1. **API Key Not Set**:

   ```bash
   export ANTHROPIC_API_KEY="your-key"
   ```

2. **Model Not Found**:

   ```python
   # Check available models
   from vericoding.core import get_available_models
   models = get_available_models()
   print(list(models.keys()))
   ```

3. **Context Too Large**:

   ```python
   # Check if text fits
   from vericoding.core import can_fit_in_context
   fits = can_fit_in_context("claude-3-5-sonnet-20241022", text)
   ```

4. **Performance Issues**:
   - Use smaller models for simple tasks
   - Monitor token usage
   - Consider chunking for extremely large content

## Future Enhancements

- More accurate token counting
- Advanced chunking strategies
- Context compression techniques
- Multi-model parallel processing
- Cost optimization algorithms




