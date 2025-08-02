# LLM Provider Support for spec_to_code.py

The `spec_to_code.py` script now supports multiple LLM providers including Claude (Anthropic), OpenAI, and DeepSeek.

## Supported Providers

### 1. Claude (Anthropic) - Default
- **Provider ID**: `claude`
- **Default Model**: `claude-3-5-sonnet-20241022`
- **Environment Variable**: `ANTHROPIC_API_KEY`
- **Installation**: Already included (anthropic>=0.58.2)

### 2. OpenAI
- **Provider ID**: `openai`
- **Default Model**: `gpt-4o`
- **Environment Variable**: `OPENAI_API_KEY`
- **Installation**: `pip install openai` or `pip install .[openai]`

### 3. DeepSeek
- **Provider ID**: `deepseek`
- **Default Model**: `deepseek-chat`
- **Environment Variable**: `DEEPSEEK_API_KEY`
- **Installation**: `pip install openai` (uses OpenAI-compatible API)

## Usage Examples

### Basic Usage (Default Claude)
```bash
python spec_to_code.py dafny ./specs
```

### Using OpenAI
```bash
python spec_to_code.py dafny ./specs --llm-provider openai
```

### Using OpenAI with Specific Model
```bash
python spec_to_code.py dafny ./specs --llm-provider openai --llm-model gpt-4o-mini
```

### Using DeepSeek
```bash
python spec_to_code.py dafny ./specs --llm-provider deepseek
```

### Using Claude with Specific Model
```bash
python spec_to_code.py dafny ./specs --llm-provider claude --llm-model claude-3-5-sonnet-20241022
```

## Environment Setup

### Option 1: Environment Variables
```bash
export ANTHROPIC_API_KEY="your-anthropic-key"
export OPENAI_API_KEY="your-openai-key"
export DEEPSEEK_API_KEY="your-deepseek-key"
```

### Option 2: .env File
Create a `.env` file in your project directory:
```env
ANTHROPIC_API_KEY=your-anthropic-key
OPENAI_API_KEY=your-openai-key
DEEPSEEK_API_KEY=your-deepseek-key
```

## Installation

### Base Installation (Claude only)
```bash
pip install -e .
```

### With OpenAI Support
```bash
pip install -e .[openai]
```

### With All Providers
```bash
pip install -e .[all]
```

## Architecture

The LLM provider system uses an abstract interface (`LLMProvider`) with concrete implementations:

- `AnthropicProvider`: Uses the official Anthropic SDK
- `OpenAIProvider`: Uses the official OpenAI SDK
- `DeepSeekProvider`: Uses OpenAI SDK with DeepSeek's API endpoint

The factory function `create_llm_provider()` handles provider creation and API key validation.

## Error Handling

The script will provide helpful error messages if:
- Required API keys are missing
- Required packages are not installed
- Invalid provider names are specified
- API calls fail

## Rate Limiting

All providers respect the `--api-rate-limit-delay` parameter to avoid overwhelming the APIs.

## Model Defaults

Each provider has sensible defaults, but you can override them:

- **Claude**: `claude-3-5-sonnet-20241022`
- **OpenAI**: `gpt-4o`
- **DeepSeek**: `deepseek-chat`

## Adding New Providers

To add a new LLM provider:

1. Create a new class inheriting from `LLMProvider`
2. Implement `call_api()` and `get_required_env_var()` methods
3. Add the provider to the `provider_configs` in `create_llm_provider()`
4. Update the argument parser choices
5. Update this documentation
