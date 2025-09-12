# YAML to Lean Translation

This directory contains all the files needed for translating YAML specifications to Lean 4 code.

## Contents

### Core Translation Files

- **`translate_yaml_to_lean.py`** - Main translator script that converts YAML specifications to Lean 4
- **`test_translation.py`** - Test script to verify the translation functionality
- **`test_api_key.py`** - Script to validate API key configuration

### Prompt and Configuration

- **`prompts.yaml`** - Claude prompt template and configuration settings
- **`prompt_loader.py`** - Module to load and manage prompts from the YAML file

### Documentation

- **`README_translation.md`** - Detailed documentation for the translation process
- **`requirements_translation.txt`** - Python dependencies required for translation

## Architecture

The translation system is now separated into:

1. **Code Logic** (`translate_yaml_to_lean.py`) - Handles file processing, API calls, and error handling
2. **Prompt Management** (`prompts.yaml` + `prompt_loader.py`) - Manages Claude prompts and configuration
3. **Configuration** (`prompts.yaml`) - Centralized settings for model, tokens, retries, etc.

## Usage

### Setup

1. Install dependencies:

   ```bash
   pip install -r requirements_translation.txt
   ```

2. Set up your API key:

   ```bash
   export CLAUDE_API_KEY="your_api_key_here"
   ```

### Translation

Run the main translation script:

```bash
python translate_yaml_to_lean.py --api-key YOUR_API_KEY
```

### Testing

Test the translation functionality:

```bash
python test_translation.py
```

## Configuration

You can customize the translation behavior by editing `prompts.yaml`:

- **Model**: Change the Claude model used for translation
- **Parameters**: Adjust max_tokens, temperature, retries, etc.
- **Prompt**: Modify the translation prompt template
- **Rate Limiting**: Configure delays between API calls

### Example Configuration

```yaml
config:
  model: "claude-3-sonnet-20240229"
  max_tokens: 4000
  temperature: 0.1
  max_retries: 3
  rate_limit_delay: 1
```

## Features

- Translates Dafny YAML specifications to Lean 4
- Uses Claude API for high-quality translations
- Includes comprehensive error handling
- Supports batch processing of multiple files
- **Separated prompt management** for easy customization
- **Centralized configuration** for all settings

## Output

Translated files are saved to `benchmarks/vericoding_lean/yaml-depsontop-translated/`

For detailed information, see `README_translation.md`.
