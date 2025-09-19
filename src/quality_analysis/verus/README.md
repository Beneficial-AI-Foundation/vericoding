# Verus Quality Analysis Tools

This directory contains quality analysis tools specifically for Verus files (.rs and .yaml).

## Scripts

### 1. `check_verus_functions.py`
**Purpose**: Analyzes regular Verus functions to ensure they follow the expected placeholder pattern.

**What it detects**:
- ✅ **Required pattern**: Functions with exactly `{ assume(false); unreached() }`
- ⚠️ **Incomplete assume**: Functions with `assume(false)` but missing `unreached()`  
- 🚀 **Actual implementation**: Functions with real code (no `assume(false)`)

**Usage**:
```bash
# Full analysis with statistics (default directory)
python3 check_verus_functions.py

# Check single Rust file
python3 check_verus_functions.py /path/to/file.rs

# Check specific directory
python3 check_verus_functions.py /path/to/directory

# Only list files with implementations
python3 check_verus_functions.py --list-impl

# List implementations for single file
python3 check_verus_functions.py file.rs --list-impl
```

### 2. `check_spec_functions.py`
**Purpose**: Analyzes Verus spec functions in YAML files to detect those returning default values instead of proper specifications.

**Usage**:
```bash
# Full analysis with statistics (default directory)
python3 check_spec_functions.py

# Check single YAML file
python3 check_spec_functions.py /path/to/file.yaml

# Check specific directory
python3 check_spec_functions.py /path/to/directory

# Only list files with default-value spec functions
python3 check_spec_functions.py --list-defaults

# List defaults for single file
python3 check_spec_functions.py file.yaml --list-defaults

# Include problematic directories
python3 check_spec_functions.py /path/to/directory --include-problematic
```

### 3. `check_verus_types.py`
**Purpose**: Validates that executable functions in Verus YAML files use only Rust native types, not mathematical types like `Seq<int>`, `int`, `nat`.

**What it detects**:
- ❌ **Forbidden mathematical types**: `Seq<int>`, `Seq<nat>`, `int`, `nat`, etc. in executable functions
- ✅ **Valid Rust types**: `Vec<i8>`, `Vec<u8>`, `i8`, `u8`, `i32`, `u32`, etc.

**Usage**:
```bash
# Check single file
python3 check_verus_types.py /path/to/file.yaml

# Check directory
python3 check_verus_types.py /path/to/directory

# Summary only
python3 check_verus_types.py /path/to/directory --summary

# JSON output
python3 check_verus_types.py /path/to/directory --output json
```

## Expected Patterns

### Regular Functions
```rust
fn some_function(...) -> ReturnType {
    assume(false);
    unreached()
}
```

### Spec Functions (in YAML vc-preamble)
```rust
spec fn some_spec(...) -> bool {
    // Meaningful logical specification
    forall|i: int| 0 <= i < len ==> condition(i)
}
```

## Common Issues

### ❌ Problematic Patterns
```rust
// Regular function - missing unreached()
fn bad_function() -> int {
    assume(false);
}

// Spec function - default value
spec fn bad_spec() -> int { 0 }
spec fn bad_predicate() -> bool { true }

// Executable function - forbidden mathematical types
fn bad_executable(arr: Seq<int>) -> (result: nat) { ... }
```

### ✅ Good Patterns
```rust
// Regular function - proper placeholder
fn good_function() -> int {
    assume(false);
    unreached()
}

// Spec function - meaningful logic
spec fn good_spec(seq: Seq<int>) -> bool {
    forall|i: int| 0 <= i < seq.len() ==> seq[i] >= 0
}

// Executable function - Rust native types
fn good_executable(arr: Vec<i8>) -> (result: u8) { ... }
```