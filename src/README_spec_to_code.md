# Unified Specification-to-Code Processing

This document describes the unified `spec_to_code.py` script that replaces the three language-specific scripts for Dafny, Lean, and Verus.

## Overview

The unified script consolidates the functionality of:
- `dafny/spec_to_code.py`
- `lean/spec_to_code_lean.py`
- `verus/spec_to_code.py`

Into a single script that accepts the language as a command-line parameter.

## Key Changes

### 1. Language Configuration File

All language-specific settings are now defined in `config/language_config.toml`:
- File extensions (`.dfy`, `.lean`, `.rs`)
- Tool paths and environment variables
- Verification commands
- Success/failure indicators
- Language-specific keywords
- Specification preservation patterns

### 2. Command-Line Interface

The new interface requires specifying the language as the first argument:

```bash
# Old way (language-specific scripts)
python dafny/spec_to_code.py ./specs
python lean/spec_to_code_lean.py ./benchmarks/lean/dafnybench
python verus/spec_to_code.py ./benchmarks/verus_specs

# New way (unified script)
python spec_to_code.py dafny ./specs
python spec_to_code.py lean ./benchmarks/lean/dafnybench
python spec_to_code.py verus ./benchmarks/verus_specs
```

### 3. Language-Specific Handling

The script handles language differences through:

1. **Configuration-driven behavior**: Most differences are handled through the configuration file
2. **Special file filtering**: Lean files are only processed if they contain 'sorry'

### 4. Environment Variables

Each language uses its own environment variable for the tool path:
- Dafny: `DAFNY_PATH`
- Lean: `LEAN_PATH`
- Verus: `VERUS_PATH`

### 5. Prompts Files

The script looks for prompts files based on the language configuration:
- Dafny: `prompts.yaml` (in dafny directory)
- Lean: `prompts-lean.yaml` (in lean directory)
- Verus: `prompts.yaml` (in verus directory)

## Usage Examples

```bash
# Basic usage
python spec_to_code.py dafny ./specs

# With options
python spec_to_code.py lean ./specs --iterations 3 --debug
python spec_to_code.py verus ./specs --workers 8 --strict-specs

# All available options
python spec_to_code.py <language> <folder> \
    --iterations 5 \      # Max verification attempts (default: 5)
    --debug \            # Save intermediate files
    --strict-specs \     # Enable strict specification preservation
    --workers 4          # Number of parallel workers (default: 4)
```

## Migration Guide

To migrate from the old scripts to the unified script:

1. **Update your scripts/workflows**:
   - Add the language as the first argument
   - Keep all other arguments the same

2. **Environment variables remain the same**:
   - No changes needed to `DAFNY_PATH`, `LEAN_PATH`, or `VERUS_PATH`

3. **Output directory structure**:
   - The unified script adds the language name to the output path
   - Example: `src/code_from_spec_on_30-07_15h30/verus/autoverus/`

4. **Prompt files**:
   - Continue using the same prompt files in their current locations
   - The script automatically finds them based on the language

## Extending to New Languages

To add support for a new language:

1. Add a new section to `config/language_config.toml`
2. Add any special file filtering logic in `find_spec_files()`
3. Create appropriate prompts file
