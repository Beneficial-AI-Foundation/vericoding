# Vericode Verus Framework

A comprehensive AI-powered framework for generating and verifying Verus code from specifications. This framework iteratively calls Large Language Models (LLMs) to generate Rust code that satisfies Verus specifications.

## Overview

The Vericode Verus framework is designed to:
- Process Verus specification files containing TODO comments
- Generate implementations for functions marked with TODO
- Preserve all specifications (ensures/requires clauses) exactly
- Verify generated code using Verus
- Provide detailed feedback and debugging information
- Support iterative refinement of generated code

## Features

- **Specification Preservation**: Maintains all ensures/requires clauses exactly as specified
- **TODO Implementation**: Automatically implements functions marked with TODO comments
- **Iterative Verification**: Multiple verification attempts with automatic error fixing
- **Debug Mode**: Saves intermediate files for debugging and analysis
- **Comprehensive Reporting**: Generates detailed reports with success rates and error analysis
- **API Flexibility**: Supports both Claude and OpenAI APIs
- **Batch Processing**: Processes entire directories of Verus files

## Installation

### Prerequisites

1. **Python 3.7+**
2. **Verus**: Install Verus following the [official instructions](https://verus-lang.github.io/verus/install/)
3. **Cargo**: Rust's package manager (usually installed with Rust)
4. **API Keys**: Either Anthropic API key (for Claude) or OpenAI API key

### Setup

1. Clone the repository:
```bash
git clone <repository-url>
cd vericoding/verus
```

2. Install Python dependencies:
```bash
pip install requests pyyaml
# For OpenAI support (optional)
pip install openai
```

3. Set up environment variables:
```bash
export ANTHROPIC_API_KEY="your-anthropic-api-key"
# OR for OpenAI
export OPENAI_API_KEY="your-openai-api-key"
```

## Usage

### Basic Usage

Process a directory of Verus files:
```bash
python vericoder_verus.py ./benchmarks/VerusProofSynthesisBench/MBPP/
```

### Advanced Options

```bash
python vericoder_verus.py \
  --verbose \
  --output-dir ./results \
  --model claude-sonnet-4-20250514 \
  --iterations 3 \
  --debug \
  --strict-todos \
  --relaxed-specs \
  ./benchmarks/
```

### Command Line Options

- `-v, --verbose`: Enable verbose output
- `--strict-todos`: Strict verification of TODO blocks (default: enabled)
- `--relaxed-todos`: Relaxed verification of TODO blocks
- `--strict-specs`: Strict verification of specifications (default: enabled)
- `--relaxed-specs`: Relaxed verification of specifications
- `--output-dir DIR`: Output directory for results
- `--max-retries N`: Maximum number of retries per file (default: 3)
- `--timeout N`: Timeout in seconds for API calls (default: 120)
- `--api-delay N`: Delay between API calls in seconds (default: 2.0)
- `--model MODEL`: LLM model to use (default: claude-sonnet-4-20250514)
- `--api-key KEY`: API key (or set environment variables)
- `--temperature T`: Temperature for LLM generation (default: 0.1)
- `--max-tokens N`: Maximum tokens for LLM response (default: 8192)
- `--iterations N`: Maximum verification attempts per file (default: 1)
- `--debug`: Enable debug mode (save intermediate files)

## Input Format

The framework expects Verus files with the following structure:

```rust
use vstd::prelude::*;

verus! {

spec fn is_even(n: u32) -> (result: bool) {
    (n % 2) == 0
}

fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
```

Key elements:
- **TODO comments**: Functions that need implementation
- **Spec functions**: `spec fn` declarations that should be preserved
- **Proof functions**: `proof fn` declarations for proofs
- **Ensures clauses**: Postconditions that must be satisfied
- **Requires clauses**: Preconditions that must be met

## Output Structure

The framework generates several output files:

```
output_directory/
├── impl_*.rs              # Generated implementations
├── debug/                 # Debug files (if debug mode enabled)
│   └── filename/
│       ├── original.rs    # Original input file
│       ├── generated.rs   # Initial LLM output
│       ├── final.rs       # Final processed code
│       └── iter_*.rs      # Iteration-specific versions
├── results_*.json         # Detailed results in JSON format
├── results.csv           # Summary results in CSV format
└── summary.txt           # Human-readable summary
```

## Verification Process

1. **File Discovery**: Finds all `.rs` files containing Verus code
2. **Code Analysis**: Extracts TODO blocks and specifications
3. **LLM Generation**: Calls the LLM to generate implementations
4. **Specification Preservation**: Ensures all specs are maintained
5. **Verification**: Runs `cargo check` with Verus
6. **Iterative Refinement**: Attempts fixes if verification fails
7. **Result Reporting**: Generates comprehensive reports

## Error Handling

The framework handles various types of errors:

- **API Errors**: Network issues, rate limits, authentication problems
- **Compilation Errors**: Syntax errors, type mismatches, missing imports
- **Verification Errors**: Failed postconditions, loop invariants, termination measures
- **Specification Errors**: Modified ensures/requires clauses

## Debugging

Enable debug mode to save intermediate files:
```bash
python vericoder_verus.py --debug ./benchmarks/
```

This creates a `debug/` directory with:
- Original input files
- LLM-generated code
- Final processed code
- Iteration-specific versions

## Configuration

### Environment Variables

- `ANTHROPIC_API_KEY`: Anthropic API key for Claude
- `OPENAI_API_KEY`: OpenAI API key for GPT models
- `VERUS_PATH`: Path to Verus executable (default: verus)
- `CARGO_PATH`: Path to Cargo executable (default: cargo)

### Prompt Customization

Edit `prompts-verus.yaml` to customize the prompts used for code generation and error fixing.

## Examples

### Simple Example

Input file `task_804.rs`:
```rust
use vstd::prelude::*;

verus! {

spec fn is_even(n: u32) -> (result: bool) {
    (n % 2) == 0
}

fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
```

Generated implementation:
```rust
use vstd::prelude::*;

verus! {

spec fn is_even(n: u32) -> (result: bool) {
    (n % 2) == 0
}

fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> !is_even(#[trigger] arr[k]),
    {
        if is_even(arr[i]) {
            return true;
        }
        i = i + 1;
    }
    return false;
}

} // verus!

fn main() {}
```

## Troubleshooting

### Common Issues

1. **Verus not found**: Ensure Verus is installed and in your PATH
2. **API key issues**: Check that your API key is set correctly
3. **Compilation errors**: Verify that the input files are valid Verus code
4. **Verification timeouts**: Increase the timeout value for complex specifications

### Getting Help

- Check the debug output for detailed error information
- Review the generated intermediate files
- Examine the verification output for specific error messages
- Use verbose mode for more detailed logging

## Contributing

To contribute to the Verus vericoding framework:

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests if applicable
5. Submit a pull request

## License

This project is licensed under the same terms as the main vericoding repository.

## Acknowledgments

- Verus team for the excellent verification framework
- Anthropic and OpenAI for providing the LLM APIs
- The vericoding community for feedback and contributions 