# Selected 100 Hoare Specification Files (No Polynomials)

This folder contains 100 carefully selected Hoare specification files from the `all_hoare_specs` directory that do **not** involve:

- Floating point mathematical functions (sin, cos, tan, log, exp, sqrt, etc.)
- Polynomial operations (Hermite, Chebyshev, Legendre, Laguerre polynomials)

## Contents

- **100 Lean files** - Hoare specification files (.lean)
- **README.md** - This file

## Selection Criteria

The files were selected based on the following criteria:

1. **Excluded**: Files containing floating point mathematical functions (sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, log, exp, sqrt)
2. **Excluded**: Files with "mathematical_functions" in the filename
3. **Excluded**: Files with "fft" (Fast Fourier Transform) in the filename
4. **Excluded**: Files with polynomial operations:
   - "hermite" - Hermite polynomials
   - "chebyshev" - Chebyshev polynomials
   - "legendre" - Legendre polynomials
   - "laguerre" - Laguerre polynomials
5. **Included**: Files focusing on practical operations like:
   - String operations
   - Array manipulation
   - Indexing and slicing
   - Bitwise operations
   - Sorting and searching
   - Statistics
   - Linear algebra (basic operations)
   - Data type routines
   - I/O operations
   - Set operations
   - Random number generation
   - And more

## Statistics

- **Total files in all_hoare_specs**: 719
- **Files with floating point functions**: 168
- **Files with polynomial operations**: 133 (additional)
- **Total excluded files**: 301
- **Files selected**: 100
- **Remaining files available**: 418

## File Categories

The selection includes files from the following categories:

### String Operations (15+ files)

- String manipulation and transformation
- Case conversion, replacement, translation
- String validation and checking

### Array Manipulation (20+ files)

- Array creation and copying
- Array reshaping and transformation
- Broadcasting and splitting operations
- Matrix operations

### Indexing and Slicing (10+ files)

- Various indexing operations
- Diagonal extraction
- Multi-dimensional indexing
- Where operations

### Linear Algebra (5+ files)

- Basic matrix operations
- QR decomposition
- Least squares
- Eigenvalues
- Matrix multiplication

### Statistics (3+ files)

- Histograms
- Averages and percentiles
- Statistical operations

### Bitwise Operations (3+ files)

- Bitwise AND, OR operations
- Shift operations

### Sorting and Searching (2+ files)

- Sort and argsort operations

### Data Type Routines (5+ files)

- Type conversion and manipulation
- Type promotion and finding

### I/O Operations (3+ files)

- File and data I/O operations

### Other Categories (30+ files)

- Random number generation
- Set operations
- Numpy operations
- Ufuncs
- Typing operations
- And various other practical operations

## Benefits of This Selection

1. **No Complex Mathematics**: Excludes all floating point functions and polynomial operations
2. **Practical Focus**: Concentrates on commonly used data processing operations
3. **String Processing**: Good coverage of string operations
4. **Array Operations**: Comprehensive array manipulation coverage
5. **Basic Linear Algebra**: Essential matrix operations without complex computations
6. **Data Processing**: Focus on data transformation and manipulation

## Usage

These files can be used for:

- Testing verification systems
- Benchmarking formal verification tools
- Educational purposes in formal methods
- Development of Hoare logic specifications
- Array and string processing verification
- Data processing verification

## Comparison with Previous Selection

This selection is more restrictive than the previous one:

- **Previous**: Excluded only floating point functions (168 files excluded)
- **Current**: Excludes floating point functions + all polynomial operations (301 files excluded)

This makes the current selection more focused on practical data processing operations without any complex mathematical computations.
