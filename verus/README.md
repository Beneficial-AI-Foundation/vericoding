# Verus Translation Project

This project provides tools and infrastructure for translating Dafny specifications into Verus, a formal verification system for Rust. The project focuses on automated translation of formal specifications while preserving their semantic meaning and verification properties.

## Project Structure

```
verus/
├── Cargo.toml           # Rust project configuration and dependencies
├── src/
│   ├── dafny_spec_to_verus_translator.py  # Core translation logic
│   ├── dafny_to_verus_llm.py              # LLM-assisted translation
│   ├── compare_specs.py                    # Specification comparison tool
│   ├── run_verus_checks.py                # Verification script for Verus specs
│   ├── verus_specs/                        # LLM-translated specifications
│   │   └── translations/                   # Organized by category
│   └── verus_specs_no_llm/                # Direct translations without LLM
│       └── translations/                   # Organized by category
├── diffs/                                  # Specification comparison results
└── logs/                                   # Verification results and logs
```

## Dependencies

The project requires:

- Verus (version specified in Cargo.toml)
- Python 3.x for translation scripts
- Rust toolchain (2021 edition)

Core Rust dependencies (from Cargo.toml):
- `vstd`
- `builtin`
- `builtin_macros`

## Features

### 1. Dafny to Verus Translation

The project provides two translation approaches:

- **Direct Translation** (`dafny_spec_to_verus_translator.py`):
  - Converts Dafny types to Verus types
  - Translates predicates and methods
  - Handles arrays, sequences, and maps
  - Preserves requires/ensures clauses

- **LLM-Assisted Translation** (`dafny_to_verus_llm.py`):
  - Uses language models for more sophisticated translations
  - Better handles complex specifications
  - Maintains semantic equivalence

### 2. Specification Categories

Translations are organized into several categories:

- `atomizer_supported/`: Core specifications with atomizer support
- `clover/`: Clover-related specifications
- `simple_specs/`: Basic specification examples
- `synthesis_task/`: Synthesis-related specifications

### 3. Verification and Comparison

- `compare_specs.py`: Tools for comparing different translations
- Logging system for tracking verification results
- Diff generation for specification comparisons

## Usage

- **Running Translations**:
  ```bash
  python src/dafny_spec_to_verus_translator.py  # For direct translation
  # or
  python src/dafny_to_verus_llm.py             # For LLM-assisted translation
  ```

- **Compiling Generated Specs**:
  ```bash
  python src/run_verus_checks.py
  ```
  This will:
  - Check all Rust files in the specs directory
  - Generate detailed logs in the `logs` directory
  - Provide statistics on successful/failed verifications
  - Create a JSON report with verification results

- **Comparing Specifications**:
  ```bash
  python src/compare_specs.py
  ```

