# Dafny Quality Analysis Tools

This directory contains quality analysis tools specifically for Dafny YAML files with embedded code.

## Scripts

### 1. `check_dafny_functions.py`
**Purpose**: Analyzes functions and predicates in `vc-preamble` sections for default values.

**Key Features**:
- ✅ **YAML-based parsing**: More reliable than raw Dafny parsing
- ✅ **vc-preamble focus**: Analyzes functions/predicates in YAML vc-preamble sections  
- ✅ **Brace counting**: Handles complex nested function bodies correctly

**What it detects**:
- 🚀 **Proper specification**: Functions/predicates with meaningful logical content
- ⚠️ **Default value**: Functions/predicates returning simple defaults (0, false, empty collections)
- 🔄 **Placeholder**: Functions/predicates that are empty or incomplete

**Usage**:
```bash
# Full analysis with statistics (default directory)
python3 check_dafny_functions.py

# Check single YAML file
python3 check_dafny_functions.py /path/to/file.yaml

# Check specific directory
python3 check_dafny_functions.py /path/to/directory

# Only list files with default-value functions
python3 check_dafny_functions.py --list-defaults

# List defaults for single file
python3 check_dafny_functions.py file.yaml --list-defaults

# Include problematic directories
python3 check_dafny_functions.py /path/to/directory --include-problematic
```

### 2. `check_dafny_methods.py`
**Purpose**: Analyzes methods in `vc-code` sections for implementation quality.

**Key Features**:
- ✅ **Method-focused**: Specifically targets method implementations in vc-code sections
- ✅ **Assume false detection**: Correctly identifies `assume {:axiom} false` patterns
- ✅ **Implementation detection**: Finds methods with actual code instead of placeholders

**What it detects**:
- ✅ **Using assume false** (expected): Methods with `assume {:axiom} false;` pattern
- 📝 **Has actual implementation**: Methods with real code instead of placeholders

**Usage**:
```bash
# Full analysis with statistics (default directory)
python3 check_dafny_methods.py

# Check single YAML file
python3 check_dafny_methods.py /path/to/file.yaml

# Check specific directory
python3 check_dafny_methods.py /path/to/directory

# Only list files with method implementations
python3 check_dafny_methods.py --list-implementations

# List implementations for single file
python3 check_dafny_methods.py file.yaml --list-implementations
```

### 3. `show_dafny_examples.py`
**Purpose**: Shows detailed examples of problematic Dafny functions/predicates with context.

**Features**:
- Shows exact line numbers and function signatures
- Displays problematic function bodies with context
- Provides improvement suggestions

**Usage**:
```bash
# Show examples using generated file list
python3 show_dafny_examples.py

# Customize output
python3 show_dafny_examples.py --max-files 10 --max-per-file 3

# Use custom file list
python3 show_dafny_examples.py --file-list my_defaults.txt
```

## Expected Patterns

### Methods (in YAML vc-code)
```dafny
vc-code: |-
  {
    assume {:axiom} false;
  }
```

### Functions/Predicates (in YAML vc-preamble)
```dafny
vc-preamble: |-
  function compute_value(x: int): int
      requires x > 0
  {
      // Meaningful computation
      if x == 1 then 1 else x * compute_value(x - 1)
  }
  
  predicate valid_input(s: string)
  {
      // Meaningful validation
      |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] != '\0'
  }
```

**Note**: Both scripts focus on YAML files, not raw `.dfy` files, as this provides more reliable parsing and better coverage of the verification codebase.

## Common Issues

### ❌ Problematic Patterns
```dafny
// Method with actual implementation (should use assume false)
method bad_method() returns (result: int)
{
    result := 42;  // Should be: assume {:axiom} false;
}

// Function with default value
function bad_function(): int { 0 }

// Predicate always returning true
predicate bad_validation(s: string) { true }
```

### ✅ Good Patterns
```dafny
// Method with proper assumption
method good_method() returns (result: int)
    ensures result > 0
{
    assume {:axiom} false;
}

// Function with meaningful logic
function good_function(x: int): int
    requires x >= 0
{
    if x == 0 then 1 else x * good_function(x - 1)
}

// Predicate with actual validation
predicate good_validation(nums: seq<int>)
{
    |nums| > 0 && forall i :: 0 <= i < |nums| ==> nums[i] >= 0
}
```

## File Types Supported

- **`.dfy` files**: Direct Dafny source files
- **`.yaml` files**: YAML files with embedded Dafny code in sections like:
  - `vc-preamble`: Helper functions and predicates
  - `vc-spec`: Method signatures with contracts
  - `vc-code`: Method implementations

## Output Files

### From check_dafny_functions.py:
- `dafny_functions_with_defaults.txt`: YAML files with functions/predicates returning default values
- `dafny_functions_with_placeholders.txt`: YAML files with placeholder functions
- `dafny_proper_specifications.txt`: YAML files with meaningful function specifications

### From check_dafny_methods.py:
- `dafny_methods_with_implementations.txt`: YAML files with methods having actual implementations
- `dafny_methods_with_assume_false.txt`: YAML files with methods using expected assume false pattern

## Why YAML Analysis?

The Dafny scripts focus on YAML files because:

1. **More reliable**: YAML parsing is simpler and less error-prone than raw Dafny syntax parsing
2. **Better coverage**: Most verification work in this project uses YAML format with embedded Dafny code
3. **Cleaner extraction**: `vc-preamble` and `vc-code` sections contain the functions/methods in well-defined structures
4. **Accurate results**: YAML approach correctly identified 161/161 methods as using assume false vs. 0/161 with mixed parsing

The split approach provides focused analysis: functions/predicates (specifications) vs. methods (implementations).

## Integration Notes

These tools work particularly well with:
- HumanEval Dafny benchmarks
- Apps benchmarks
- Translated verification tasks
- YAML-embedded Dafny specifications
