# Dafny Specification-to-Code Processing

This tool automatically generates verified Dafny implementations from specifications using Claude AI. It processes Dafny files containing `//ATOM` and `//SPEC` blocks, generates implementations, and verifies them iteratively.

## Features

- **Automatic Code Generation**: Converts Dafny specifications to verified implementations
- **Iterative Verification**: Multiple verification attempts with automatic error fixing
- **ATOM Block Preservation**: Preserves existing verified code blocks exactly
- **GitHub Integration**: Generates CSV with links to spec and implementation files
- **Debug Mode**: Saves intermediate files for analysis

## Prerequisites

1. **Python 3.7+** 
   **Dependencies**:
   ```bash
   pip install requests pyyaml
   ```
2. **Dafny** - Must be installed and available in PATH
3. **Anthropic API Key** - For Claude AI access

## File Format

Your Dafny files should use the following block structure:

### Basic Format and Code Block Types

- **`//ATOM`**: Existing verified code that should be preserved exactly
- **`//SPEC`**: Specifications that need implementation
- **`//SPEC [name]`**: Named specifications (optional)
- **`//CONSTRAINTS:`**: Additional constraints for implementation (optional)

See `prompts.yaml` and benchmark folders for examples.

## Usage

### Basic Usage and Command Line Options

```bash
python spec_to_code.py FOLDER [OPTIONS]

Arguments:
  FOLDER                  Directory with .dfy specification files

Options:
  --iterations, -i N     Max verification attempts per file (default: 5)
  --debug                Enable debug mode (save intermediate files)
  --strict-atoms        Enable strict ATOM block verification (default: relaxed)
  --help                Show help message
```

### Examples

```bash
# Basic usage with defaults
python spec_to_code.py ./specs

# Process files with 3 iterations
python spec_to_code.py ./numpy_specs --iterations 3

# Process files with debug mode and 5 iterations
python spec_to_code.py ./test --debug --iterations 5


## Output

### Generated Files

The tool creates a timestamped output directory:

```
benchmarks/numpy_specs/code_from_spec_on_19-06_15h24/
├── results.csv                    # Success/failure summary with GitHub links
├── summary.txt                    # Detailed processing summary
├── np_abs_impl.dfy               # Generated implementation
├── np_add_impl.dfy               # Generated implementation
└── ... (other implementation files)
```

### Debug Mode Files

When `--debug` is enabled, additional files are saved:

```
code_from_spec_on_19-06_15h24/
├── np_abs_iter_0_original.dfy    # Original specification
├── np_abs_iter_1_generated.dfy   # Initial generated code
├── np_abs_iter_1_current.dfy     # Code after iteration 1
├── np_abs_iter_2_current.dfy     # Code after iteration 2
└── np_abs_impl.dfy               # Final implementation
```

### CSV Results

The `results.csv` file contains:

| Column | Description |
|--------|-------------|
| `spec_name` | Original specification filename |
| `spec_to_code` | `success` or `failed` |
| `spec_link` | GitHub link to original spec file |
| `impl_link` | GitHub link to generated implementation |

Example:
```csv
"spec_name","spec_to_code","spec_link","impl_link"
"np_abs.dfy","success","https://github.com/.../np_abs.dfy","https://github.com/.../np_abs_impl.dfy"
```

## Configuration

### Environment Variables

- `ANTHROPIC_API_KEY`: Required for Claude AI access
- `DAFNY_PATH`: Path to Dafny executable (default: `dafny`)

## How It Works

1. **Read Specifications**: Parse Dafny files with `//ATOM` and `//SPEC` blocks
2. **Generate Code**: Use Claude AI to implement `//SPEC` blocks
3. **Preserve ATOMs**: Keep `//ATOM` blocks unchanged
4. **Verify**: Run Dafny verification on generated code
5. **Iterate**: If verification fails, fix errors and retry
6. **Output**: Save final implementations and generate reports

### Debug Mode

Enable debug mode to see intermediate files:
```bash
python spec_to_code.py ./specs --debug
```

This saves files after each iteration, helping identify where issues occur.

## File Structure

```
dafny/
├── spec_to_code.py           # Main processing script
├── prompts.yaml              # AI prompts configuration
├── prompt_loader.py          # Prompt loading utility
├── benchmarks/
│   ├── numpy_specs/          # Example specifications
│   └── bignum_specs/         # Example specifications
└── tools/                    # Additional utilities
```

