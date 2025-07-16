# Lean 4 Verification Code

This directory contains Lean 4 implementations and specifications for various verification benchmarks.

## Contents

- `benchmarks/` - Formal specifications of algorithms and data structures
  - `dafny-bench_specs/` - Lean 4 ports of Dafny specifications (110+ algorithms)

## Overview

The Lean 4 code in this repository demonstrates formal verification techniques using:
- Dependent types for strong specifications
- Hoare triple notation for imperative-style specifications
- Theorem proving for algorithm correctness

## Getting Started

1. Install Lean 4 and Lake build system
2. Navigate to a specific benchmark directory
3. Run `lake build` to verify compilation
4. Implement proofs for the specifications (currently marked as `sorry`)

## Contributing

Contributions are welcome! Please:
- Follow existing code style and conventions
- Ensure all files compile before submitting
- Document any significant changes or additions
- Add appropriate test cases where applicable

## Related Work

This complements the existing verification efforts in:
- `/dafny/` - Original Dafny specifications
- `/lean-vc/` - Earlier Lean verification work

The goal is to provide a comprehensive suite of formally verified algorithms across multiple verification systems.