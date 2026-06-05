# Inspection Analysis Summary

This document summarizes the manual inspection of 120 vericoding outputs across all language/benchmark combinations.

## Methodology

For each language (Dafny, Lean, Verus) and benchmark, 5 vericoding outputs were sampled uniformly at random from successful runs. Each sample was analyzed for:
1. **Issues with spec** - Whether the specification was correct, weak, or mistranslated
2. **Issues with implementation** - Whether the implementation had problems

## Spec Classification Summary

| Classification | Count | Percentage |
|----------------|-------|------------|
| **[None]** | 84 | 70.0% |
| **[Leak]** | 15 | 12.5% |
| **[Weak]** | 14 | 11.7% |
| **[Mistranslated]** | 7 | 5.8% |
| **Total** | 120 | 100% |

## Implementation Classification Summary

| Classification | Count | Percentage |
|----------------|-------|------------|
| **[None]** | 104 | 86.7% |
| **[Extra]** | 7 | 5.8% |
| **[Others]** | 9 | 7.5% |
| **Total** | 120 | 100% |

## Classification Definitions

### [None]
Spec is correct and unmodified. No issues detected.

### [Leak]
Implementation details leak into the specification, making it trivially implementable. Examples include:
- Spec can be used directly as implementation
- Specification already includes a solution

### [Weak]
Spec has omissions leading to easier or trivial problems. Examples include:
- Missing `ensures` clauses
- Uses `assume {:axiom} false` or `{:axiom}` markers (unverified)
- Spec permits trivial solutions
- Loses constraints during transpilation

### [Mistranslated]
Type changes or semantic differences from the original spec. Examples include:
- Float → i32 type changes during transpilation
- Superimposes/merges functions incorrectly
- Logical changes (e.g., `∃ k, x = 2*k` → `x % 2 == 0`)

### Implementation Classifications

#### [None]
No issues with implementation. Code is correct and well-structured.

#### [Extra]
Implementation includes unnecessary additional code. Examples include:
- Unused helper functions or predicates
- Unused lemmas
- Functions added but not required by the spec

#### [Others]
Other issues with the implementation. Examples include:
- Uses `assume(false)` or `assume {:axiom}` to bypass verification
- Task function absent from implementation
- Stub implementations (e.g., functions returning hardcoded values)
- Missing loop invariants making verification incomplete
- Verbose or redundant code/proofs
- Overly restrictive preconditions
- Function name typos

## Results by Language

### Dafny (40 samples)

| Benchmark | [None] | [Leak] | [Weak] | [Mistranslated] |
|-----------|--------|--------|--------|-----------------|
| apps | 3 | 0 | 2 | 0 |
| bignum | 5 | 0 | 0 | 0 |
| dafnybench | 5 | 0 | 0 | 0 |
| humaneval | 5 | 0 | 0 | 0 |
| numpy_simple | 3 | 0 | 0 | 2 |
| numpy_triple | 4 | 0 | 1 | 0 |
| verified-cogen | 5 | 0 | 0 | 0 |
| verina | 3 | 1 | 0 | 1 |
| **Total** | **33** | **1** | **3** | **3** |

#### Dafny Implementation Issues

| Benchmark | [None] | [Extra] | [Others] |
|-----------|--------|---------|----------|
| apps | 4 | 0 | 1 |
| bignum | 5 | 0 | 0 |
| dafnybench | 3 | 0 | 2 |
| humaneval | 2 | 2 | 1 |
| numpy_simple | 3 | 1 | 1 |
| numpy_triple | 4 | 0 | 1 |
| verified-cogen | 3 | 2 | 0 |
| verina | 5 | 0 | 0 |
| **Total** | **29** | **5** | **6** |

### Lean (40 samples)

| Benchmark | [None] | [Leak] | [Weak] | [Mistranslated] |
|-----------|--------|--------|--------|-----------------|
| appstest | 1 | 3 | 1 | 0 |
| bignum | 2 | 3 | 0 | 0 |
| dafnybench | 1 | 3 | 1 | 0 |
| humaneval | 4 | 0 | 1 | 0 |
| numpy3 | 4 | 1 | 0 | 0 |
| numpys | 5 | 0 | 0 | 0 |
| verifcogen | 2 | 3 | 0 | 0 |
| verina | 4 | 0 | 1 | 0 |
| **Total** | **23** | **13** | **4** | **0** |

#### Lean Implementation Issues

| Benchmark | [None] | [Extra] | [Others] |
|-----------|--------|---------|----------|
| appstest | 5 | 0 | 0 |
| bignum | 5 | 0 | 0 |
| dafnybench | 5 | 0 | 0 |
| humaneval | 3 | 2 | 0 |
| numpy3 | 5 | 0 | 0 |
| numpys | 5 | 0 | 0 |
| verifcogen | 5 | 0 | 0 |
| verina | 5 | 0 | 0 |
| **Total** | **38** | **2** | **0** |

### Verus (40 samples)

| Benchmark | [None] | [Leak] | [Weak] | [Mistranslated] |
|-----------|--------|--------|--------|-----------------|
| apps | 2 | 1 | 2 | 0 |
| bignum | 3 | 0 | 0 | 2 |
| dafnybench | 4 | 0 | 0 | 1 |
| humaneval | 5 | 0 | 0 | 0 |
| numpy-simple | 3 | 0 | 2 | 0 |
| numpy_triple | 2 | 0 | 2 | 1 |
| verified-cogen | 5 | 0 | 0 | 0 |
| verina | 4 | 0 | 1 | 0 |
| **Total** | **28** | **1** | **7** | **4** |

#### Verus Implementation Issues

| Benchmark | [None] | [Extra] | [Others] |
|-----------|--------|---------|----------|
| apps | 5 | 0 | 0 |
| bignum | 2 | 0 | 3 |
| dafnybench | 5 | 0 | 0 |
| humaneval | 5 | 0 | 0 |
| numpy-simple | 5 | 0 | 0 |
| numpy_triple | 5 | 0 | 0 |
| verified-cogen | 5 | 0 | 0 |
| verina | 5 | 0 | 0 |
| **Total** | **37** | **0** | **3** |

## Key Findings

### 1. Implementation Leaks are Most Common in Lean
- 13 out of 40 Lean samples (32.5%) have implementation leaks
- Primary cause: "spec can be used as implementation" - specs are so specific they are trivially implementable
- This is a characteristic of how Lean specs were written, not a transpilation issue

### 2. Mistranslated Specs are Most Common in Verus
- 4 out of 40 Verus samples (10%) have mistranslated specs
- Primary causes:
  - Type system differences (Float → i32)
  - Function merging issues in bignum benchmark
  - Ghost type (`int`) used in exec function context

### 3. Dafny Has Fewest Issues
- 33 out of 40 (82.5%) have no spec issues
- Most benchmarks were originally written in Dafny or designed for it

### 4. Implementation Issues by Language
- **Lean has fewest implementation issues**: 38/40 (95%) have no issues
- **Verus [Others] issues**: 3/40 (7.5%) - verbose proofs, overly restrictive preconditions, external_body usage
- **Dafny has some [Extra] issues**: 5/40 (12.5%) - unused helpers and lemmas

### 5. Notable Problem Patterns

#### assume(false) / {:axiom} Usage
Some implementations use `assume(false)` or `{:axiom}` to bypass verification:
- DS0024 (NpHistogram): Main histogram method uses `assume {:axiom} false`
- DS0048 (NpShape): ShapeArrays is marked `{:axiom}` (unverified)
- VD0014 (BST insert): `insert_recursion` uses `assume(false)` - completely unverified
- DH0123: Implements unused SumElementsWithAtMostTwoDigits with assume false

#### Trivial Solutions Permitted
Some specs are weak enough to permit trivial solutions:
- DA0355: Specification permits trivial solution, likely unintended
- VT0250: Both specs admit the same trivial solution

#### Type Mismatches in Transpilation
- VT0273: Floats change to i32 in transpilation

#### Task Function Absent
Some Verus implementations fail to implement the required function:
- VB0001, VB0005: Implemented another function instead of the task function
- VB0027: Task function absent, specification trivialized

#### Stub Implementations
- DT0202: RealToString is a stub returning "0" or "1" regardless of actual value

## Recommendations

1. **Fix Lean implementation leaks** - Many specs can be used directly as implementations
2. **Improve type handling in Verus transpilation** - Float/real types need better handling
3. **Audit for assume(false)** - Some "successful" verifications are not actually verified
4. **Add spec validation** - Check that specs are not trivially satisfiable

## Files

Each benchmark folder contains:
- `analysis.yaml` - Detailed analysis of 5 sampled files
- Copied source files for human inspection
