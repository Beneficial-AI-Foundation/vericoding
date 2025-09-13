# Dafny Benchmarks - Lean Translation

This directory contains Lean 4 translations of Dafny specifications.

## File Organization

### Manually Fixed Files 
These files have been manually reviewed and fixed for syntax errors, type issues, and other compilation problems. They include:

- Binary search implementations
- Array manipulation functions
- Sorting algorithms
- String processing functions
- Mathematical computations
- Tree operations

Common problems faced during Dafny-to-Lean translations:

- Syntax errors
- Type mismatches
- Missing imports
- Incorrect function signatures
- Array indexing issues

## Translation Notes

The files were automatically translated from Dafny specifications and then manually corrected. Common issues that were fixed include:

1. **String operations**: Changed `.size` to `.length` for String types
2. **Array indexing**: Fixed `⟨...⟩` syntax to proper `[i]!` indexing
3. **Type conversions**: Added proper Int/Nat conversions where needed
4. **Function signatures**: Corrected parameter types and return types
5. **Import statements**: Added missing imports for required types

## Usage

To work with these files:

1. Start with the manually fixed files in the root directory as examples
2. Use them as reference for fixing similar issues in the remaining files
3. Each file contains both the function definition and its specification theorem
4. All functions use `sorry` as placeholder implementations

## Contributing

When fixing files in the `remaining/` directory:

1. Move fixed files to the root directory
2. Update this README with the count of fixed files
3. Document any new patterns or issues discovered
4. Test that the files compile with `lake build`
