# Verus-Bench

This is a benchmark suite for [Verus](https://github.com/verus-lang/verus), a formal verification tool.

## Overview

Verus-Bench contains 150 verification tasks from four different sources:

| Source | Tasks | Description |
|--------|-------|-------------|
| [CloverBench](https://github.com/ChuyueSun/Clover) | 11 | Selected from a collection of 60 classic CS examples originally written for Dafny |
| [MBPP](https://github.com/Mondego/dafny-synthesis) | 78 | Translated from MBPP-DFY-153, a dataset of problems with formal specifications |
| [Diffy](https://figshare.com/articles/code/Diffy_Inductive_Reasoning_of_Array_Programs_using_Difference_Invariants/14509467?file=27797196) | 38 | Array and loop verification programs from SV-COMP-2021 |
| Misc | 23 | Collection from Verus tutorials and libraries including sorting, searching, and nested loop examples |

## Structure

Each benchmark folder is organized as follows:

```
benchmarks/
├── CloverBench/     # CloverBench problems
├── MBPP/       # MBPP problems
├── Diffy/      # Diffy problems
└── Misc/       # Misc problems
```

Each source folder contains:
- `unverified/` - Tasks without proof annotations to be solved
- `verified/` - The same tasks with correct proof annotations for reference

## Task Selection Process

- **CloverBench**: From 39 Verus translations, we excluded 3 incompatible with the latest Verus, 4 with weaker specs than existing variants, and 21 verifiable without annotations.
- **MBPP**: From 153 problems, we excluded 67 requiring no proof annotations and 8 with features poorly supported in Rust/Verus (floating points, string operations).
- **Diffy**: From 69 C programs, we excluded 31 requiring non-linear equation reasoning and translated the rest to Rust.
- **Misc**: Curated collection of algorithmic problems and challenging verification examples.
