# Code2Verus

An extension of [Quinn's tool](https://github.com/Beneficial-AI-Foundation/dafny2verus) to translate code from various verification languages (Dafny, Lean) to [Verus](https://verus-lang.github.io/verus/guide/overview.html) using AI models.

## Overview

Code2Verus uses large language models to automatically translate verification code from languages like Dafny and Lean to Verus, a verification-aware Rust framework. The tool supports both Hugging Face datasets and local folders as input sources.

## Features 

### Features inherited from Quinn's dafny2verus

- **Parallel processing**: Concurrent translation with configurable limits
- **Success tracking**: Tracks successful translations to avoid reprocessing
- **Smart folder structure detection**: Handles both flat and hierarchical folder structures
- **Iterative improvement**: Uses AI tools to refine translations until they verify
- **Modular architecture**: Well-organized codebase for easy maintenance and extension

### New features

- **Multi-language support**: Translate from Dafny or Lean to Verus
- **Flexible input sources**: 
  - Hugging Face datasets (e.g., `wendy-sun/DafnyBench`, `sunblaze-ucb/verina`)
  - Local folders with code files

## How It Works

Code2Verus leverages AI models (currently Gemini) with a sophisticated iterative translation process:

1. **Input Processing**: The tool accepts input from either:
   - Hugging Face datasets (automatically downloads and parses)
   - Local folders (recursively scans for matching files)

2. **Translation Pipeline**:
   - Extracts source code from the input
   - Sends code to the AI model with language-specific prompts
   - The AI agent has access to specialized tools:
     - `verus_tool`: Compiles and verifies Verus code
     - `dafny_tool`: Validates Dafny syntax and semantics
   - Iteratively refines the translation based on verification feedback

3. **Verification Loop**:
   - Each translation attempt is verified using the actual Verus compiler
   - If verification fails, the error messages are fed back to the AI
   - The AI uses this feedback to fix issues and improve the translation
   - This continues for up to `max_translation_iterations` (configurable in `config.yml`) or until verification succeeds

4. **Success Tracking**:
   - Successful translations are recorded to avoid reprocessing
   - For hierarchical folders: Individual `success.yml` files per directory
   - For flat folders: Single consolidated `success.json` file

5. **Parallel Processing**:
   - Multiple files are processed concurrently (configurable limit)
   - Automatic retry with exponential backoff for rate-limited requests
   - Semaphore-based concurrency control to prevent overwhelming the API

The tool's modular architecture separates concerns:
- **Agent module**: Manages AI model interaction
- **Verification module**: Handles Verus compilation and verification
- **Processing module**: Orchestrates the async translation pipeline
- **Success tracking module**: Persists translation results

## Installation

### Prerequisites

1. **Python 3.12+**
2. **Verus**: Install from [https://github.com/verus-lang/verus](https://github.com/verus-lang/verus)
3. **API Keys**: Set up environment variables for AI model access (see Configuration)

### Install with uv (recommended)

```bash
# Clone the repository
git clone https://github.com/Beneficial-AI-Foundation/code2verus.git
cd code2verus

# Create virtual environment
uv venv

# Activate virtual environment
source .venv/bin/activate  # On Linux/Mac
# or
.venv\Scripts\activate  # On Windows

# Install the package
uv pip install -e .
```

### Install with pip

```bash
# Clone the repository
git clone https://github.com/Beneficial-AI-Foundation/code2verus.git
cd code2verus

# Create virtual environment
python -m venv .venv
source .venv/bin/activate  # On Linux/Mac

# Install the package
pip install -e .
```

## Configuration

### Environment Variables

Create a `.env` file in the project root:

```bash
ANTHROPIC_API_KEY=your_anthropic_api_key_here
# Add other API keys as needed
```

### Config File

The `config.yml` file contains:
- Model configurations
- System prompts for different languages
- Tool configurations
- Verus path settings
- `max_translation_iterations`: Maximum number of verification attempts per file (default: 3)
- `max_retries`: Maximum number of API retry attempts with exponential backoff (default: 16)

### Claude AI Guidance Files

The project includes specialized guidance files for Claude AI:

- **`CLAUDE_DAFNY.md`**: Provides Claude with context about Dafny-to-Verus translation patterns, common idioms, and best practices (inherited from Quinn's dafny2verus)
- **`CLAUDE_LEAN.md`**: Contains Lean-specific translation guidance for Claude

These files are part of the AI-assisted development workflow and help maintain consistency in translations when using Claude for code assistance.

## Usage

### Basic Usage

```bash
# Use default DafnyBench dataset
code2verus

# Translate from a specific Hugging Face dataset
code2verus --benchmark wendy-sun/DafnyBench --language dafny

# Translate Lean code from Verina dataset
code2verus --benchmark sunblaze-ucb/verina --language lean --split train

# Translate from a local folder
code2verus --benchmark ./benches/bignum_specs --language dafny

# Use custom file pattern for local folders
code2verus --benchmark ./my_code --file-pattern "*.dfy"

# Increase concurrent translations
code2verus --max-concurrent 5

# Process only the first 10 files
code2verus --limit 10
```

### Debug and Analysis Usage

```bash
# Save debug contexts for later analysis
code2verus --save-debug

# Generate debug reports after each translation
code2verus --debug-report

# Print overall debug summary at the end
code2verus --debug-summary

# Save debug sessions to a custom directory
code2verus --save-debug --debug-dir ./my_debug_sessions

# Comprehensive debugging with all options
code2verus --save-debug --debug-report --debug-summary --include-debug-in-result

# Debug a specific local benchmark
code2verus --benchmark ./test_cases --debug-report --debug-summary

# Monitor performance during production runs
code2verus --save-debug --debug-dir ./production_logs --debug-summary
```

### Command Line Options

#### Basic Options
- `--benchmark`: Hugging Face dataset path or local folder path (default: `wendy-sun/DafnyBench`)
- `--split`: Dataset split to use for Hugging Face datasets (default: `test`)
- `--language`: Source language to translate from (`dafny` or `lean`, default: `dafny`)
- `--max-concurrent`: Maximum number of concurrent translations (default: 3)
- `--file-pattern`: File pattern(s) to match when loading from local folder (default: `*.dfy`)
- `--limit`: Maximum number of files to process (default: process all files)

#### Debug Options
- `--save-debug`: Save detailed debug contexts to JSON files for later analysis
- `--debug-dir DIR`: Directory to save debug sessions (default: `debug_sessions`)
- `--debug-report`: Generate and print debug reports after each translation
- `--debug-summary`: Print comprehensive debug summary at the end of processing
- `--include-debug-in-result`: Include debug context in translation results (uses more memory)

## Project Structure

```
code2verus/
├── src/code2verus/
│   ├── __init__.py          # Main entry point and CLI
│   ├── agent.py             # AI agent creation and translation
│   ├── benchmarks.py        # Dataset loading logic
│   ├── config.py            # Configuration management
│   ├── processing.py        # Async processing and main loop
│   ├── success_tracker.py   # Track successful translations
│   ├── tools.py             # AI tool definitions
│   ├── utils.py             # Utility functions
│   └── verification.py      # Verus verification logic
├── artifacts/               # Output directory for translations
├── benches/                # Local benchmark files
├── config.yml              # Main configuration file
├── pyproject.toml          # Python package configuration
├── CLAUDE_DAFNY.md        # Claude AI guidance for Dafny translations
├── CLAUDE_LEAN.md         # Claude AI guidance for Lean translations
└── README.md               # This file
```

## Output

Translated files are saved in the `artifacts/` directory, organized by benchmark name:

```
artifacts/
├── dafnybench/
│   ├── example1.rs
│   ├── example2.rs
│   └── success.yml    # Tracks successful translations
└── bignum_specs/
    ├── spec1.rs
    ├── spec2.rs
    └── success.json   # For flat folder structures
```

## Success Tracking

The tool tracks successful translations to avoid reprocessing:
- **Hierarchical folders**: Individual `success.yml` files in each subdirectory
- **Flat folders**: Single `success.json` file at the benchmark root

## Debugging and Analysis

Code2verus includes comprehensive debugging capabilities to help understand and optimize the translation process:

### Debug Features

- **Session Tracking**: Each translation session gets a unique ID and detailed tracking
- **Comprehensive Timestamping**: 
  - Session start/end times with millisecond precision
  - Individual event timestamps for every conversation, error, and attempt
  - Last activity tracking and duration calculations
  - Human-readable formatted timestamps
- **Performance Metrics**: Timing, iteration counts, success rates, and resource usage
- **Error Analysis**: Categorized error types, patterns, and failure progression
- **Conversation Logs**: Complete AI conversation history with token counts and timestamps
- **Structured Data**: All debug information stored in JSON format for analysis

### Debug File Structure

```
debug_sessions/
├── debug_session_uuid1_20250909_172500.json
├── debug_session_uuid2_20250909_172501.json
└── ...
```

### Example Debug Output

When using `--debug-report`, you'll see output like:

```
=== Debug Report for Item 0 ===

# Translation Debug Report

## Session Summary
- Session ID: 02acdd35-300c-41b4-a5f2-ac5a90755643
- Source Language: dafny
- Start Time: 2025-09-09 17:24:15.123
- End Time: 2025-09-09 17:25:00.456
- Duration: 45.333 seconds
- Iterations: 3/5
- Final Status: success

## Performance Metrics
- Average iteration time: 15.11 seconds
- Success rate: 100%
- Total conversation chars: 12,847

## Error Analysis
- Total errors: 2
- Error types: verification

## Iteration Breakdown
- Iteration 1: ✗ Failed (verification) at 17:24:20.234
- Iteration 2: ✗ Failed (verification) at 17:24:35.567
- Iteration 3: ✓ Success at 17:24:50.890

## Timing Breakdown
- Exchange 1: 17:24:15.234 (1,234 chars)
- Exchange 2: 17:24:35.678 (2,156 chars)
- Exchange 3: 17:24:50.912 (1,890 chars)
```

### Programmatic Analysis

```python
from code2verus.debug_utils import load_debug_context, analyze_debug_context

# Load and analyze a debug session
debug_context = load_debug_context("debug_sessions/debug_session_xyz.json")
analysis = analyze_debug_context(debug_context)

print(f"Success rate: {analysis['performance_metrics']['success_rate']:.2%}")
print(f"Common errors: {analysis['error_patterns']['common_errors']}")
```

For complete debugging documentation, see [CLI_DEBUG_GUIDE.md](CLI_DEBUG_GUIDE.md) and [DEBUG_SYSTEM_README.md](DEBUG_SYSTEM_README.md).

## Development

### Running Tests

```bash
# Run specific test scripts
python test_folder_structure.py
python test_filename_logic.py
```

### Module Organization

- `agent.py`: Handles AI model interaction and code translation
- `benchmarks.py`: Manages dataset loading from various sources
- `processing.py`: Contains the main async processing loop
- `success_tracker.py`: Tracks and persists translation success
- `verification.py`: Interfaces with Verus for code verification

## Troubleshooting

### Verus Not Found
If you get "Verus is not installed or not in PATH":
1. Ensure Verus is installed: [https://github.com/verus-lang/verus](https://github.com/verus-lang/verus)
2. Add Verus to your PATH or update `verus_path` in `config.yml`

### API Rate Limits
If you encounter rate limits:
- Reduce `--max-concurrent` to limit parallel requests
- The tool automatically retries with exponential backoff

### Missing API Keys
Ensure all required API keys are set in your `.env` file

## Lean YAML Translation

When translating Lean YAML files to Verus YAML, Code2Verus applies semantic equivalence mapping to preserve formal verification semantics while adapting to Verus syntax and structure.

### YAML Structure Mapping

The tool automatically handles the structural differences between Lean and Verus YAML formats:

#### Direct Field Mappings
These fields maintain the same name but their content is translated:

| Lean Field | Verus Field | Translation |
|------------|-------------|-------------|
| `vc-description` | `vc-description` | Lean `/- ... -/` comments → Rust `/* ... */` comments |
| `vc-preamble` | `vc-preamble` | Lean imports → Verus imports (`use vstd::prelude::*;` + `verus! {`) |
| `vc-helpers` | `vc-helpers` | Lean helper functions → Verus equivalents |
| `vc-postamble` | `vc-postamble` | Lean closing → Verus closing (`}` + `fn main() {}`) |

#### Transformation Mappings
These fields are combined and restructured to match Verus semantics:

| Lean Fields | Verus Field | Transformation |
|-------------|-------------|----------------|
| `vc-signature` + `vc-implementation` | `vc-spec` | Function signature + contracts (`requires`/`ensures` clauses) |
| `vc-condition` + `vc-proof` | `vc-code` | Postconditions → placeholder implementation with `assume(false)` |

### Translation Rules

#### Comment Formatting
- **Lean**: `/- multiline comment -/`
- **Verus**: `/* multiline comment */`

#### Placeholder Implementations
For `vc-code` sections, always use the pattern:
```rust
{
    // impl-start
    assume(false);
    [appropriate_default_return_value]
    // impl-end
}
```

**Default return values**:
- Boolean functions: `false`
- Vec/Array functions: `Vec::new()`
- Integer functions: `0`

#### Function Contracts
- Lean preconditions (`removeElement_precond`) → Verus `requires` clauses
- Lean postconditions (`removeElement_postcond`) → Verus `ensures` clauses
- Lean theorems (`removeElement_spec_satisfied`) → Integrated into function contract

#### Example Translation

**Lean YAML Input**:
```yaml
vc-signature: |-
  def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
vc-implementation: |-
  -- <vc-implementation>
    sorry
  -- </vc-implementation>
vc-condition: |-
  @[reducible, simp]
  def removeElement_postcond (s : Array Int) (k : Nat) (result: Array Int) :=
    result.size = s.size - 1 ∧
    (∀ i, i < k → result[i]! = s[i]!) ∧
    (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)
```

**Verus YAML Output**:
```yaml
vc-spec: |-
  fn remove_element(s: &Vec<i32>, k: usize) -> (result: Vec<i32>)
      requires k < s.len(),
      ensures
          result.len() == s.len() - 1,
          forall|i: int| 0 <= i < k ==> result[i] == s[i],
          forall|i: int| k <= i < result.len() ==> result[i] == s[i + 1],
vc-code: |-
  {
      // impl-start
      assume(false);
      Vec::new()
      // impl-end
  }
```

### Implementation Details

The semantic equivalence mapping is implemented through a centralized configuration approach:

1. **`config.yml`**: Contains all prompts and instructions:
   - `system_prompts`: Language-specific system prompts for the AI agent
   - `yaml_instructions`: YAML-specific translation instructions for each language
   - `default_prompts`: Default instructions for non-YAML translations

2. **`agent.py`**: Dynamically constructs prompts from config based on language and format type

This centralized approach ensures consistency, maintainability, and eliminates prompt duplication. The formal verification semantics are preserved while adapting to Verus's syntax and verification patterns.