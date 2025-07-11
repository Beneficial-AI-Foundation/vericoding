# Lean 4 Benchmark Specifications

This directory contains Lean 4 ports of various benchmark specifications from the vericoding project.

## Structure

- `dafny-bench_specs/` - Lean 4 ports of Dafny benchmark specifications
  - 110+ formally specified algorithms ported from Dafny to Lean 4
  - Uses Hoare triple notation for specifications
  - Covers sorting, searching, data structures, and classic algorithms

## Dafny Benchmark Ports

The `dafny-bench_specs/` directory contains Lean 4 translations of Dafny specifications originally found in `/dafny/benchmarks/dafny-bench_specs/atomizer_supported/`.

### Features

- **Specification Style**: Uses Hoare triple notation from `Std.Do.Triple`
- **Type Safety**: Leverages Lean 4's dependent type system
- **Categories Covered**:
  - Basic operations (arithmetic, comparisons)
  - Array algorithms (sorting, searching, transformations)
  - String operations
  - Data structures (BST, maps, sets)
  - LeetCode-style problems
  - Classic verification examples

### Usage

These specifications serve as:
1. Reference implementations for correct algorithms
2. Test cases for verification tools
3. Educational resources for formal methods
4. Bridge between Dafny and Lean 4 communities

### Building

To use these specifications in a Lean 4 project:

1. Add the necessary imports (e.g., `Std.Do.Triple`)
2. Import specific algorithm files as needed
3. Implement the algorithms and prove the specifications

### Contributing

When adding new specifications:
- Follow the existing naming conventions
- Use Hoare triple style for specifications
- Document deviations from original Dafny specs
- Ensure files compile with `lake build`

See `dafny-bench_specs/CLAUDE.md` for detailed porting methodology and guidelines.