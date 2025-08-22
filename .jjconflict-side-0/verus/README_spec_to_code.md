# Verus Specification-to-Code Processing

This directory contains adapted versions of the Dafny specification-to-code processing tools for Verus (a formal verification system for Rust).

## Files

- `prompts.yaml` - Verus-specific prompts for code generation and verification fixing
- `spec_to_code.py` - Main script for processing Verus specification files

## Key Adaptations from Dafny

### Language Differences
- **File Extension**: `.rs` instead of `.dfy`
- **Verification Tool**: Uses `verus` binary instead of `dafny`
- **Syntax**: Adapted for Verus/Rust syntax:
  - `requires()`, `ensures()`, `invariant()` instead of Dafny syntax
  - `spec fn` for specification functions
  - `pub fn` for public functions
  - `proof { ... }` blocks for complex proofs
  - `unimplemented!()` for placeholder implementations

### Verification Process
- First runs compilation check with `--no-verify` flag
- Then runs full verification if compilation succeeds
- Handles both compilation and verification errors

### Code Structure
- Preserves ATOM/SPEC/IMPL block structure from Dafny version
- ATOM blocks contain specification functions and predicates
- SPEC blocks contain function signatures with contracts
- IMPL blocks contain actual implementations

## Usage

```bash
# Basic usage
python spec_to_code.py ./path/to/verus/specs

# With custom iterations and debug mode
python spec_to_code.py ./specs --iterations 3 --debug

# With strict ATOM block verification
python spec_to_code.py ./specs --strict-atoms
```

## Requirements

- Python 3.x
- Verus binary (set VERUS_PATH environment variable)
- ANTHROPIC_API_KEY environment variable
- PyYAML for prompt loading

## Environment Variables

- `VERUS_PATH`: Path to Verus binary (defaults to expected location)
- `ANTHROPIC_API_KEY`: Required for LLM API calls

## Output

The script generates:
- `*_impl.rs` files with implementations
- Summary and CSV reports
- Debug files (when debug mode enabled)

## Differences from Dafny Version

1. **Verification Commands**: Uses Verus-specific command line flags
2. **Error Detection**: Adapted for Rust/Verus error messages
3. **Code Extraction**: Recognizes Verus-specific keywords and patterns
4. **File Handling**: Processes `.rs` files instead of `.dfy`
5. **Syntax Fixes**: Handles Verus-specific incomplete code patterns
