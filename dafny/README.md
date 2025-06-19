# Tool for generating verified Dafny code 

This tool automatically generates verified Dafny implementations from specifications using Claude AI. It processes Dafny files containing `//ATOM` and `//SPEC` blocks, generates implementations, and verifies them iteratively.

## Main Features

- **Automatic Code Generation**: Converts Dafny specifications to verified implementations
- **Iterative Verification**: Multiple verification attempts with automatic error fixing
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

## How It Works

1. **Read Specifications**: Parse Dafny files with `//ATOM` and `//SPEC` blocks
2. **Generate Code**: Use Claude AI to implement `//SPEC` blocks based on given prompt. See `prompts.yaml` for details.
3. **Verify**: Run Dafny verification on generated code
4. **Iterate**: If verification fails, fix errors and retry
5. **Output**: Save final implementations and generate reports

### Debug Mode

Enable debug mode to see intermediate files:
```bash
python spec_to_code.py ./specs --debug
```

This saves files after each iteration, helping identify where issues occur.

