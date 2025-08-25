# Verus Validation Features

This document describes the Verus validation functionality added to the verification coding project.

## Overview

The project now includes robust Verus syntax validation for YAML files containing Verus code. The validation ensures that:

1. YAML files can be converted back to valid Rust code
2. The generated Rust code passes Verus syntax checking
3. The code works both with and without helper functions (vc-helpers blocks)

## Shared Module: `verus_validation.py`

Contains common functionality used by both test scripts and processing scripts:

- `find_verus_executable()`: Locates Verus executable or raises `VerusNotFoundError`
- `verify_rust_with_verus()`: Runs Verus syntax check on Rust files
- `create_yaml_without_helpers()`: Creates YAML with empty vc-helpers section
- `convert_yaml_to_rust()`: Converts YAML back to Rust for validation
- `validate_yaml_with_verus()`: Complete validation pipeline for YAML content

## Scripts

### `test_verus_validation.py`

Enhanced test script that validates all YAML files in the test directory.

**Features:**
- Tests original YAML files with Verus syntax checking
- Tests modified versions with empty vc-helpers sections
- Comprehensive reporting of validation results
- **Strict error handling**: Raises exception if Verus not found

**Usage:**
```bash
# Run validation tests
uv run src/tests/test_verus_validation.py
```

### `process_verified_cogen.py`

Enhanced processing script that clones verified-cogen repository and applies filtering.

**Features:**
- Converts Rust files from verified-cogen to YAML format
- **Filtering mode**: Only includes files that pass Verus validation
- Dual output structure:
  - `output_dir/` - All converted files (for debugging)
  - `output_dir/filtered/` - Only validated files (clean dataset)
- Comprehensive logging of filtered files
- **Strict error handling**: Raises exception if Verus not found when filtering enabled

**Usage:**
```bash
# Process with filtering (requires Verus)
uv run src/process_verified_cogen.py -o /path/to/output

# Process without filtering (no Verus required)
uv run src/process_verified_cogen.py -o /path/to/output --no-filter

# Copy filtered files elsewhere
cp -r /path/to/output/filtered/* /destination/

# Check what was filtered out
cat /path/to/output/filter_log.json
```

## Error Handling

Both scripts now use strict error handling:

- **VerusNotFoundError**: Raised when Verus executable is required but not found
- **No silent failures**: Scripts will not proceed with degraded functionality
- **Clear error messages**: Include installation instructions for Verus

## Installation Requirements

### Verus Installation

Required for validation features:

```bash
# Install Verus from source
cargo install --git https://github.com/verus-lang/verus verus
```

### Python Dependencies

Already handled by existing project setup:

```bash
uv sync  # Install all project dependencies
```

## File Structure

```
src/
├── verus_validation.py          # Shared validation functionality
├── process_verified_cogen.py    # Main processing script with filtering
└── tests/
    ├── test_verus_validation.py # Validation test script
    └── verus-test-data/         # Test YAML files
```

## Benefits

1. **Quality Assurance**: Only YAML files that produce valid Verus syntax are included
2. **Reliability**: Helper function removal doesn't break code generation
3. **Debuggability**: Full logging of what gets filtered and why
4. **Flexibility**: Can process with or without filtering
5. **Maintainability**: Shared code follows DRY principles
6. **Robustness**: Clear error handling prevents silent failures

## Example Output

### Successful Filtering
```
✅ Found Verus at: verus
🔄 Converting and filtering files based on Verus validation...
Processing 100/318 files...
Processing 200/318 files...
Processing 318/318 files...

✅ Successfully converted and validated 264 files
🚫 Filtered out 54 files
❌ Failed to convert 0 files
📋 Filter log written to: /tmp/output/filter_log.json

📂 All YAML files written to: /tmp/output
✅ Validated YAML files written to: /tmp/output/filtered
📋 Filtering log available at: /tmp/output/filter_log.json

💡 To copy filtered files elsewhere:
   cp -r /tmp/output/filtered/* /your/destination/directory/
```

### Error When Verus Missing
```
❌ Verus executable not found. Please install verus or add it to PATH.
Try: cargo install --git https://github.com/verus-lang/verus verus
```