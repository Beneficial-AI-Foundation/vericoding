# Vericode Dafny - Modular Architecture

This document describes the modular architecture of the Vericode Dafny tool, which has been split into four logical modules for better maintainability and separation of concerns.

## Module Structure

### 1. `vericoder.py` - Main Orchestration Module
**Purpose**: Main entry point and orchestration of the entire process.

**Key Responsibilities**:
- Command-line argument parsing
- File processing orchestration
- OpenAI API integration
- High-level workflow management
- Error handling and retry logic

**Key Functions**:
- `main()`: Entry point with argument parsing
- `process_file()`: Process individual Dafny files
- `call_openai_api()`: OpenAI API communication
- `load_prompts()`: Load prompts from YAML file

### 2. `vericode_parser.py` - Parsing and Code Extraction Module
**Purpose**: Handle all parsing, extraction, and code manipulation operations.

**Key Responsibilities**:
- Find and read Dafny files
- Extract Dafny code from LLM responses
- Parse and extract different block types (ATOM, SPEC, IMPL)
- Separate specifications from implementation bodies
- Fix common code issues
- Detect compilation errors

**Key Functions**:
- `find_dafny_files()`: Discover .dfy files in directories
- `extract_dafny_code()`: Extract code from LLM responses
- `extract_impl_blocks()`: Extract IMPL blocks from code
- `extract_spec_blocks()`: Extract SPEC blocks from code
- `extract_atom_blocks()`: Extract ATOM blocks from code
- `extract_specification()`: Separate spec from implementation
- `extract_body()`: Extract implementation body
- `get_signature()`: Extract method/function signatures
- `merge_spec_with_body()`: Combine specs with bodies
- `fix_incomplete_code()`: Fix common code issues
- `detect_compilation_errors()`: Detect errors in responses

### 3. `vericode_checker.py` - Verification and Validation Module
**Purpose**: Handle all verification, checking, and validation operations.

**Key Responsibilities**:
- Verify Dafny files using the Dafny verifier
- Check preservation of ATOM blocks
- Verify specification preservation
- Restore original blocks when violations are detected
- Merge specifications with implementations

**Key Functions**:
- `verify_dafny_file()`: Run Dafny verification
- `verify_atom_blocks()`: Check ATOM block preservation
- `verify_specifications()`: Check specification preservation
- `restore_atom_blocks()`: Restore original ATOM blocks
- `restore_specifications()`: Restore original specifications

### 4. `vericode_printer.py` - Output and Display Module
**Purpose**: Handle all output formatting, display, and results management.

**Key Responsibilities**:
- Generate and display summaries
- Format and save results
- Print help information
- Create output directories
- Display processing progress
- Format verification results

**Key Functions**:
- `print_summary()`: Display processing summary
- `save_results()`: Save results to JSON
- `print_file_result()`: Display individual file results
- `print_help()`: Display help information
- `print_processing_header()`: Display processing information
- `print_verification_result()`: Display verification results
- `print_block_verification()`: Display block verification results
- `print_merge_info()`: Display merging information

## Usage

### Running the Tool
```bash
python3 vericoder.py [OPTIONS] <directory>
```

### Testing Individual Modules
```bash
python3 test_modules.py
```

### Importing Modules
```python
from vericode_parser import find_dafny_files, extract_dafny_code
from vericode_checker import verify_dafny_file
from vericode_printer import print_summary
```

## Dependencies

### Required Python Packages
- `openai`: OpenAI API client
- `pyyaml`: YAML file parsing
- `argparse`: Command-line argument parsing

### External Dependencies
- `dafny`: Dafny verifier (must be in PATH or set via DAFNY_PATH env var)

### Environment Variables
- `OPENAI_API_KEY`: OpenAI API key
- `DAFNY_PATH`: Path to Dafny executable (default: "dafny")

## Configuration

The tool uses `prompts.yaml` for prompt configuration and supports various command-line options:

- `--strict-atoms`: Strict ATOM block verification (default: enabled)
- `--relaxed-atoms`: Relaxed ATOM block verification
- `--strict-specs`: Strict specification verification (default: enabled)
- `--relaxed-specs`: Relaxed specification verification
- `--output-dir`: Output directory for results
- `--max-retries`: Maximum retries per file
- `--model`: LLM model to use
- `--temperature`: Generation temperature
- `--max-tokens`: Maximum response tokens

## Benefits of Modular Architecture

1. **Separation of Concerns**: Each module has a clear, focused responsibility
2. **Maintainability**: Easier to modify and extend individual components
3. **Testability**: Each module can be tested independently
4. **Reusability**: Modules can be imported and used in other projects
5. **Debugging**: Easier to isolate and fix issues
6. **Documentation**: Clear documentation for each module's purpose

## Migration from Original

The original `spec_to_code.py` file is preserved for reference. The new modular structure maintains all original functionality while providing better organization and extensibility.

## Testing

Run the test script to verify all modules work correctly:
```bash
python3 test_modules.py
```

This will test:
- Parser functions (file finding, code extraction, block parsing)
- Checker functions (verification, block checking)
- Printer functions (results formatting, help display) 