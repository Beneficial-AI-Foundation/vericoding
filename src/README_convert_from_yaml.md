# Convert from YAML Documentation

This document explains how to use the `convert_from_yaml.py` script to convert YAML specification files to different output formats.

## Overview

The `convert_from_yaml.py` script processes YAML files that contain verification code specifications and converts them to various output formats. The script supports four main conversion modes:

1. **JSON format** - Pretty-printed JSON with 2-space indentation
2. **JSONL format** - JSON Lines format for batch processing
3. **Code formats** - Direct code generation (Lean, Dafny, Rust)
4. **Directory conversion** - Batch convert all YAML files in a directory to a new directory

## YAML File Format

The script expects YAML files with the following structure:
```yaml
vc-description: |-
  Description content here...

vc-preamble: |-
  Preamble content here...

vc-helpers: |-
  Helper functions here...

vc-signature: |-
  Function signature here...

vc-implementation: |-
  Implementation code here...

vc-condition: |-
  Pre/post conditions here...

vc-proof: |-
  Proof content here...

vc-spec: |-
  Specification here...

vc-code: |-
  Additional code here...

vc-postamble: |-
  Postamble content here...
```

Each section uses the `|-` YAML literal block scalar indicator, and the content is indented with 2 spaces.

## Usage

### Basic Command Format

```bash
python convert_from_yaml.py <input_file_or_directory> --suffix <output_format> [--dir]
```

### 1. JSON Format (`--suffix json`)

Converts a single YAML file to a pretty-printed JSON file.

**Usage:**
```bash
python convert_from_yaml.py input.yaml --suffix json
```

**Output:**
- Creates `input.json` in the same directory
- JSON is formatted with 2-space indentation
- All YAML sections are preserved as JSON fields

**Example:**
```bash
python convert_from_yaml.py ../benchmarks/vericoding_raw/humaneval/HumanEval_0.yaml --suffix json
# Creates: ../benchmarks/vericoding_raw/humaneval/HumanEval_0.json
```

### 2. JSONL Format (`--suffix jsonl`)

Converts all YAML files in a directory to a single JSONL file. Each YAML file becomes one line in the JSONL file.

**Usage:**
```bash
python convert_from_yaml.py <directory_path> --suffix jsonl
```

**Output:**
- Creates `<directory_name>.jsonl` in the parent directory
- Each line contains one JSON object
- Adds an `id` field with the original YAML filename (without extension)

**Example:**
```bash
python convert_from_yaml.py ../benchmarks/vericoding_raw/humaneval/ --suffix jsonl
# Creates: ../benchmarks/vericoding_raw/humaneval.jsonl
# Each line contains one YAML file's content plus an 'id' field
```

### 3. Code Formats (`--suffix lean`, `--suffix dfy`, `--suffix rs`)

Converts a single YAML file to a specific programming language format by concatenating the relevant sections.

**Usage:**
```bash
python convert_from_yaml.py input.yaml --suffix lean
python convert_from_yaml.py input.yaml --suffix dfy
python convert_from_yaml.py input.yaml --suffix rs
```

**Output:**
- Creates `input.lean`, `input.dfy`, or `input.rs` in the same directory
- Concatenates sections in this order:
  1. `vc-description`
  2. `vc-preamble`
  3. `vc-helpers`
  4. `vc-signature`
  5. `vc-implementation`
  6. `vc-condition`
  7. `vc-proof`
  8. `vc-spec`
  9. `vc-code`
  10. `vc-postamble`

**Example:**
```bash
python convert_from_yaml.py ../benchmarks/vericoding_raw/humaneval/HumanEval_0.yaml --suffix lean
# Creates: ../benchmarks/vericoding_raw/humaneval/HumanEval_0.lean
```

### 4. Directory Conversion (`--dir` option)

Converts all YAML files in a directory to a new directory with files having the specified suffix.

**Usage:**
```bash
python convert_from_yaml.py <directory_path> --suffix <format> --dir
```

**Output:**
- Creates a new directory named `<original_dir_name>_<suffix>` in the same parent directory
- Each YAML file becomes a corresponding output file with the specified suffix
- Maintains the original file structure in the new directory

**Examples:**
```bash
# Convert all YAML files to Lean files
python convert_from_yaml.py ../benchmarks/vericoding_raw/humaneval/ --suffix lean --dir
# Creates: ../benchmarks/vericoding_raw/humaneval_lean/ with .lean files

# Convert all YAML files to Dafny files
python convert_from_yaml.py ../benchmarks/vericoding_raw/dafnybench/ --suffix dfy --dir
# Creates: ../benchmarks/vericoding_raw/dafnybench_dfy/ with .dfy files

# Convert all YAML files to JSON files
python convert_from_yaml.py ../benchmarks/vericoding_raw/humaneval/ --suffix json --dir
# Creates: ../benchmarks/vericoding_raw/humaneval_json/ with .json files
```

**Note:** The `--dir` option is not available for JSONL format (use without `--dir` for JSONL).

## Section Processing

The script processes YAML sections as follows:

1. **Line-by-line parsing** - Reads the YAML file line by line
2. **Key detection** - Identifies keys by looking for lines containing `: |-`
3. **Value extraction** - Collects all subsequent lines until the next key
4. **Indentation handling** - Removes exactly 2 spaces from the beginning of each value line
5. **Newline cleanup** - Removes trailing newlines from the final value

## Error Handling

- **File not found**: Script will raise `FileNotFoundError` if the input file doesn't exist
- **Invalid directory**: For JSONL mode, script will raise `ValueError` if the input is not a directory
- **No YAML files**: For JSONL mode, script will print a message if no `.yaml` files are found in the directory

## Examples

### Convert single file to JSON
```bash
python convert_from_yaml.py task.yaml --suffix json
```

### Convert directory to JSONL
```bash
python convert_from_yaml.py ./tasks/ --suffix jsonl
```

### Convert to Lean code
```bash
python convert_from_yaml.py task.yaml --suffix lean
```

### Convert to Dafny code
```bash
python convert_from_yaml.py task.yaml --suffix dfy
```

### Convert to Rust code
```bash
python convert_from_yaml.py task.yaml --suffix rs
```

### Convert directory to Lean files
```bash
python convert_from_yaml.py ./tasks/ --suffix lean --dir
```

### Convert directory to Dafny files
```bash
python convert_from_yaml.py ./tasks/ --suffix dfy --dir
```

### Convert directory to JSON files
```bash
python convert_from_yaml.py ./tasks/ --suffix json --dir
```

## Output File Locations

- **JSON/Code formats**: Output file is created in the same directory as the input file
- **JSONL format**: Output file is created in the parent directory of the input directory
- **Directory conversion**: New directory is created in the same parent directory as the input directory

## Notes

- The script preserves the original indentation structure while removing the 2-space YAML indentation
- Empty sections are automatically filtered out in code generation
- The JSONL format is useful for batch processing and machine learning applications
- Code generation concatenates sections in a specific order optimized for each language
- Directory conversion automatically creates the output directory if it doesn't exist
- The `--dir` option is not compatible with JSONL format (use standard JSONL conversion for batch processing)
