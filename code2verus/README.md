# Code2Verus

A generalized verification language translator that supports bidirectional translation between verification languages using AI models. Originally extended from [Quinn's tool](https://github.com/Beneficial-AI-Foundation/dafny2verus), now supports multiple translation directions including the new capability to translate from [Verus](https://verus-lang.github.io/verus/guide/overview.html) back to other verification languages.

## Overview

Code2Verus uses large language models to automatically translate verification code between languages like Dafny, Lean, and Verus. The tool supports both Hugging Face datasets and local folders as input sources, with intelligent bidirectional translation capabilities.

## Features 

### Core Translation Capabilities

- **Bidirectional Translation**: Translate between verification languages in multiple directions:
  - **Dafny ↔ Verus** (both directions supported)
  - **Lean → Verus** 
  - **Verus → Dafny** (NEW!)
  - Framework ready for additional combinations (Lean ↔ Dafny, Verus ↔ Lean)

### Features inherited from Quinn's dafny2verus

- **Parallel processing**: Concurrent translation with configurable limits
- **Success tracking**: Tracks successful translations to avoid reprocessing
- **Smart folder structure detection**: Handles both flat and hierarchical folder structures
- **Iterative improvement**: Uses AI tools to refine translations until they verify
- **Modular architecture**: Well-organized codebase for easy maintenance and extension

### Enhanced features

- **Multi-language support**: Flexible source and target language selection
- **Multiple LLM Providers**: Choose from different AI models and providers:
  - **Direct APIs**: Anthropic Claude, OpenAI GPT, xAI Grok
  - **OpenRouter**: Access to 50+ models through a single API key including Claude, GPT, Gemini, DeepSeek, and more
- **Dynamic verification**: Automatically uses appropriate verification tools for target language
- **Flexible input sources**: 
  - Hugging Face datasets (e.g., `wendy-sun/DafnyBench`, `sunblaze-ucb/verina`)
  - Local folders with code files
- **Intelligent tool selection**: Automatically selects verification tools based on translation direction

## How It Works

Code2Verus leverages AI models with a sophisticated iterative translation process:

1. **Input Processing**: The tool accepts input from either:
   - Hugging Face datasets (automatically downloads and parses)
   - Local folders (recursively scans for matching files)

2. **Translation Pipeline**:
   - Extracts source code from the input
   - Determines appropriate translation direction (source → target language)
   - Sends code to the AI model with language-specific prompts
   - The AI agent has access to specialized verification tools:
     - `verus_tool`: Compiles and verifies Verus code
     - `dafny_tool`: Validates Dafny syntax and semantics
     - `lean_tool`: Checks Lean code syntax and types

3. **Verification Loop**:
   - Each translation attempt is verified using the appropriate compiler/checker
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
- **Verification module**: Handles multiple verification tools (Verus, Dafny, Lean)
- **Processing module**: Orchestrates the async translation pipeline
- **Success tracking module**: Persists translation results

## Translation Capabilities

### Bidirectional Translation Support

Code2Verus now supports **bidirectional translation** between verification languages, making it a versatile tool for cross-language verification work:

#### Currently Supported Directions ✅
- **Dafny → Verus**: Translate Dafny specifications to Verus (original functionality)
- **Lean → Verus**: Convert Lean 4 theorems and proofs to Verus (original functionality)  
- **Verus → Dafny**: **NEW!** Reverse-translate Verus code back to Dafny

#### Framework Ready for Extensions 🚧
The system architecture supports easy addition of:
- **Verus → Lean**: Verus to Lean 4 translation
- **Dafny ↔ Lean**: Direct translation between Dafny and Lean
- **Additional Languages**: Framework ready for Coq, Isabelle/HOL, etc.

### Key Translation Features

#### Language-Specific Intelligence
- **Smart Prompt Selection**: Uses different AI prompts optimized for each translation direction
- **Semantic Preservation**: Maintains formal verification semantics across language boundaries
- **Contract Translation**: Properly maps `requires`/`ensures`/`invariant` clauses between languages
- **Type System Adaptation**: Handles differences in type systems and verification approaches

#### YAML Structure Handling
- **Structured Translations**: Supports YAML-format input/output for complex verification projects
- **Field Mapping**: Automatically transforms YAML field structures between language conventions
- **Specification Extraction**: Intelligently separates contracts, implementations, and proofs

#### Verification Integration
- **Multi-Tool Support**: Automatically selects appropriate verification tools (Verus, Dafny, Lean)
- **Iterative Refinement**: Uses verification feedback to improve translations
- **Error-Driven Learning**: AI learns from compiler/checker errors to fix translation issues

### Example Translation Flows

```bash
# Traditional: Other languages to Verus
dafny_spec.dfy → (AI + Verus verification) → verus_spec.rs
lean_theorem.lean → (AI + Verus verification) → verus_proof.rs

# NEW: Verus back to other languages  
verus_impl.rs → (AI + Dafny verification) → dafny_method.dfy

# Future possibilities:
dafny_spec.dfy → (AI + Lean verification) → lean_theorem.lean
```

## Installation

### Prerequisites

1. **Python 3.12+**
2. **Verification Tools** (install based on your translation needs):
   - **Verus**: Required for any Verus translation - [https://github.com/verus-lang/verus](https://github.com/verus-lang/verus)
   - **Dafny**: Required for Dafny translations - [https://github.com/dafny-lang/dafny](https://github.com/dafny-lang/dafny)
   - **Lean 4**: Required for Lean translations - [https://leanprover.github.io/lean4/doc/quickstart.html](https://leanprover.github.io/lean4/doc/quickstart.html)
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
# For direct Anthropic Claude API (default)
ANTHROPIC_API_KEY=your_anthropic_api_key_here

# OR for OpenRouter (supports multiple models)
OPENROUTER_API_KEY=your_openrouter_api_key_here

# Add other API keys as needed for direct providers
# OPENAI_API_KEY=your_openai_api_key_here
# XAI_API_KEY=your_xai_api_key_here
```

### Model Configuration

Code2Verus supports multiple LLM providers:

#### Direct Provider APIs (Default)
```yaml
# Direct Anthropic Claude (requires ANTHROPIC_API_KEY)
model: "anthropic:claude-sonnet-4-20250514"
```

#### OpenRouter Support (NEW!)
OpenRouter provides access to multiple models through a single API key. To use OpenRouter models:

1. **Set up OpenRouter API key**:
   ```bash
   export OPENROUTER_API_KEY=your_openrouter_api_key_here
   ```

2. **Configure an OpenRouter model** in `config.yml`:
   ```yaml
   # OpenRouter Claude models
   model: "openrouter:anthropic/claude-sonnet-4"
   model: "openrouter:anthropic/claude-opus-4.1"
   
   # OpenRouter GPT models  
   model: "openrouter:openai/gpt-5"
   model: "openrouter:openai/gpt-5-mini"
   model: "openrouter:openai/o1-preview"
   
   # OpenRouter other models
   model: "openrouter:deepseek/deepseek-chat-v3.1"
   model: "openrouter:google/gemini-2.5-pro" 
   model: "openrouter:google/gemini-2.5-flash"
   model: "openrouter:x-ai/grok-4"
   model: "openrouter:mistralai/mistral-medium-3.1"
   model: "openrouter:qwen/qwen3-coder-30b-a3b-instruct"
   ```

**Benefits of OpenRouter**:
- Access to models from multiple providers with one API key
- Often better pricing and rate limits
- Access to latest models from various providers
- Unified billing across different model providers

### Config File

The `config.yml` file contains:
- **Model configurations**: Specify which LLM to use (direct providers or OpenRouter)
- **System prompts**: Language-specific translation instructions for different source languages
- **Tool configurations**: Paths to verification tools (Verus, Dafny, Lean)
- **Verus path settings**: Location of Verus binary
- **Translation parameters**:
  - `max_translation_iterations`: Maximum number of verification attempts per file (default: 3)
  - `max_retries`: Maximum number of API retry attempts with exponential backoff (default: 16)

### Claude AI Guidance Files

The project includes specialized guidance files for Claude AI:

- **`CLAUDE_DAFNY.md`**: Provides Claude with context about Dafny-to-Verus translation patterns, common idioms, and best practices (inherited from Quinn's dafny2verus)
- **`CLAUDE_LEAN.md`**: Contains Lean-specific translation guidance for Claude

These files are part of the AI-assisted development workflow and help maintain consistency in translations when using Claude for code assistance.

## Usage

### Basic Translation Examples

```bash
# Default behavior: Dafny to Verus using DafnyBench dataset
code2verus

# Explicit source and target languages (recommended)
code2verus --source-language dafny --target-language verus

# NEW: Reverse translation - Verus to Dafny
code2verus --source-language verus --target-language dafny --benchmark ./my_verus_code

# Lean to Verus translation
code2verus --source-language lean --target-language verus --benchmark sunblaze-ucb/verina

# Translate from local folders
code2verus --source-language dafny --target-language verus --benchmark ./benches/dafny_specs
code2verus --source-language verus --target-language dafny --benchmark ./benches/verus_examples

# Use specific Hugging Face datasets
code2verus --source-language dafny --target-language verus --benchmark wendy-sun/DafnyBench
code2verus --source-language lean --target-language verus --benchmark sunblaze-ucb/verina --split train
```

### Advanced Usage

```bash
# Custom file patterns for different source languages
code2verus --source-language dafny --target-language verus --benchmark ./my_code --file-pattern "*.dfy"
code2verus --source-language verus --target-language dafny --benchmark ./my_code --file-pattern "*.rs"
code2verus --source-language lean --target-language verus --benchmark ./my_code --file-pattern "*.lean"

# Performance and concurrency control
code2verus --source-language verus --target-language dafny --max-concurrent 5
code2verus --source-language dafny --target-language verus --limit 10

# Processing specific dataset splits
code2verus --source-language lean --target-language verus --benchmark sunblaze-ucb/verina --split train
```

### Legacy Usage (Deprecated)

```bash
# These still work but show deprecation warnings
code2verus --language dafny    # Same as --source-language dafny --target-language verus
code2verus --language lean     # Same as --source-language lean --target-language verus
```

### Debug and Analysis Usage

```bash
# Save debug contexts for later analysis
code2verus --source-language verus --target-language dafny --save-debug

# Generate debug reports after each translation
code2verus --source-language dafny --target-language verus --debug-report

# Print overall debug summary at the end
code2verus --source-language verus --target-language dafny --debug-summary

# Save debug sessions to a custom directory
code2verus --source-language dafny --target-language verus --save-debug --debug-dir ./my_debug_sessions

# Comprehensive debugging with all options
code2verus --source-language verus --target-language dafny --save-debug --debug-report --debug-summary --include-debug-in-result

# Debug a specific local benchmark
code2verus --source-language verus --target-language dafny --benchmark ./test_cases --debug-report --debug-summary
```

### Supported Translation Combinations

Currently implemented:
- **dafny → verus** ✅ (original functionality)  
- **lean → verus** ✅ (original functionality)
- **verus → dafny** ✅ (NEW bidirectional capability)

Framework ready for future extensions:
- **verus → lean** (infrastructure in place)
- **dafny → lean** (infrastructure in place)  
- **lean → dafny** (infrastructure in place)

### Command Line Options

#### Translation Control
- `--source-language {dafny,lean,verus}`: Source language to translate from (default: `dafny`)
- `--target-language {dafny,lean,verus}`: Target language to translate to (default: `verus`)
- `--language`: **[DEPRECATED]** Legacy parameter for source language (use `--source-language` instead)

#### Input/Output Options
- `--benchmark`: Hugging Face dataset path or local folder path (default: `wendy-sun/DafnyBench`)
- `--split`: Dataset split to use for Hugging Face datasets (default: `test`)
- `--file-pattern`: File pattern(s) to match when loading from local folder (auto-detected based on source language)
- `--limit`: Maximum number of files to process (default: process all files)

#### Performance Options  
- `--max-concurrent`: Maximum number of concurrent translations (default: 3)

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

Translated files are saved in the `artifacts/` directory, with organization depending on the target language and benchmark structure:

### Output Structure for Different Target Languages

```
artifacts/
├── dafny_to_verus/         # Dafny → Verus translations
│   ├── example1.rs
│   ├── example2.rs
│   └── success.yml
├── verus_to_dafny/         # Verus → Dafny translations (NEW!)
│   ├── example1.dfy
│   ├── example2.dfy  
│   └── success.yml
├── lean_to_verus/          # Lean → Verus translations  
│   ├── example1.rs
│   ├── example2.rs
│   └── success.yml
└── benchmark_results.yml   # Overall results tracking
```

### File Extensions by Target Language

- **Target: Verus** → `.rs` files (Rust/Verus code)
- **Target: Dafny** → `.dfy` files (Dafny code)  
- **Target: Lean** → `.lean` files (Lean code)
- **YAML mode** → `.yaml` files (structured YAML with code sections)

### Example Output Structures

**Dafny to Verus (default):**
```
artifacts/
├── dafnybench/
│   ├── algorithms/
│   │   ├── sort.rs
│   │   └── search.rs
│   └── success.yml
```

**Verus to Dafny (reverse translation):**
```
artifacts/  
├── verus_examples/
│   ├── verification/
│   │   ├── invariants.dfy
│   │   └── contracts.dfy
│   └── success.yml
```

**Lean to Verus:**
```
artifacts/
├── verina_dataset/
│   ├── basic/
│   │   ├── types.rs
│   │   └── functions.rs
│   └── success.yml
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
├── debug_session_dafny_to_verus_success_iter3_20250910_175002_38bd434b.json
├── debug_session_verus_to_dafny_failed_iter1_20250910_174659_67d45538.json
├── debug_session_lean_to_verus_success_iter2_20250910_180125_02acdd35.json
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

### Verification Tool Issues

#### Verus Not Found
If you get "Verus is not installed or not in PATH":
1. Ensure Verus is installed: [https://github.com/verus-lang/verus](https://github.com/verus-lang/verus)
2. Add Verus to your PATH or update `verus_path` in `config.yml`

#### Dafny Not Found  
If you get "Dafny is not installed or not in PATH" when using `--target-language dafny`:
1. Ensure Dafny is installed: [https://github.com/dafny-lang/dafny](https://github.com/dafny-lang/dafny)
2. Add Dafny to your PATH or update `dafny_path` in `config.yml`
3. Verify installation: `dafny --version`

#### Lean Not Found
If you get "Lean is not installed or not in PATH" when using `--source-language lean` or `--target-language lean`:
1. Ensure Lean 4 is installed: [https://leanprover.github.io/lean4/doc/quickstart.html](https://leanprover.github.io/lean4/doc/quickstart.html)
2. Add Lean to your PATH or update `lean_path` in `config.yml`
3. Verify installation: `lean --version`

### Translation Issues

#### Unsupported Language Combinations
If you get "Translation from X to Y is not yet supported":
- Check the currently supported combinations in the help: `code2verus --help`
- Currently supported: `dafny→verus`, `dafny→lean`, `lean→verus`, `verus→dafny`
- Additional combinations can be added by extending the system prompts in `config.yml`

#### File Pattern Mismatches
If no files are found in local directories:
- Check that `--file-pattern` matches your source files
- Auto-detection: `.dfy` for Dafny, `.lean` for Lean, `.rs` for Verus
- Use explicit patterns: `--file-pattern "*.rs"` for Verus files

### Performance Issues

#### API Rate Limits
If you encounter rate limits:
- Reduce `--max-concurrent` to limit parallel requests
- The tool automatically retries with exponential backoff

#### Memory Usage
For large datasets:
- Avoid `--include-debug-in-result` unless needed for analysis
- Use `--limit` to process smaller batches
- Monitor memory usage with `--debug-summary`

### Configuration Issues

#### Missing API Keys
Ensure all required API keys are set in your `.env` file:
```bash
ANTHROPIC_API_KEY=your_key_here
# Add other API keys as needed
```

#### Configuration File Issues
If you get configuration errors:
- Verify `config.yml` syntax is valid YAML
- Check that all required paths are correctly specified
- Use absolute paths if relative paths cause issues

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